-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_Supplement_Numerics
-- name    : GibbsTransition_SizeCopies_Supplement_Numerics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:36:35.364921+00:00
-- url     : https://prove2.me/theorems/04cf892c-47c0-480f-9ace-715cde70aab6
-- title:
--   Rational Schur elimination and deterministic finite-energy search
-- statement:
--   Rational complex entries use the quadratic algebra $\mathbb Q[i]$. The finite-energy computation constructs the dense matrix from rational local terms, represents a Hermitian complex matrix by its real symmetric block matrix, tests positive definiteness by recursive exact Schur elimination, and bisects a rational spectral interval. Nonpositive pivots, including singular equality cases, reject positive definiteness.
--   $$\widehat s=-\frac{\widetilde e_L(\phi+h)-\widetilde e_L(\phi-h)}{2h},\qquad h=\gamma/2,\quad L=\lceil16C_*/(d\gamma)\rceil,\quad \zeta=d\gamma/32.$$
--   The comparison with $(a+b)/2$ drives the same overlapping search. The approximation premise is exactly the preceding uniform energy bound $|\widehat e_L-(e_u-c_u)|\le\Delta+C_*/L$, with $C_*=\max(1,12J)$ and the explicit scalar shift $c_u$.
--
--   All dense cubes in this module are computed classically. They consume no copies or supplied spins, and the procedure receives rational reconstructed terms rather than exact thermodynamic energies.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), (52)–(54),(78)–(79), Appendix B.5, printed pp. 14–15,24–25 (PDF pp. 16–17,26–27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Recovery
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_GroundLearner
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false

noncomputable section

namespace GibbsTransition.SizeCopies.Supplement
attribute [local instance] Classical.propDecidable

/-- Exact rational complex arithmetic; i²=-1. No real spectral oracle is used
by the finite-energy computation. -/
abbrev QC := QuadraticAlgebra ℚ (-1) 0
abbrev QMatrix (n : Type) := Matrix n n QC

def qc (a b : ℚ) : QC := ⟨a,b⟩
def qReal (a : ℚ) : QC := qc a 0
def qcComplex (z : QC) : ℂ := (z.re : ℂ) + (z.im : ℂ)*Complex.I

def complexMatrix {n : Type} (A : QMatrix n) : Matrix n n ℂ := fun i j => qcComplex (A i j)
def qScale {n : Type} (r : ℚ) (A : QMatrix n) : QMatrix n := fun i j => qReal r * A i j

def qTraceFree {n : Type} [Fintype n] [DecidableEq n] (A : QMatrix n) : QMatrix n :=
  A - qScale (1 / (Fintype.card n : ℚ)) ((Matrix.trace A) • (1 : QMatrix n))

structure RationalTerms (q : ℕ) where
  onsite : QMatrix (Fin q)
  edge : Fin 3 → QMatrix (Fin q × Fin q)
  effect : QMatrix (Fin q)

def complexTerms {q : ℕ} (r : RationalTerms q) : FieldInteraction q :=
  ⟨complexMatrix r.onsite, fun i => complexMatrix (r.edge i)⟩

def RationalHermitian {q : ℕ} (r : RationalTerms q) : Prop :=
  (complexMatrix r.onsite).IsHermitian ∧
  (∀ i, (complexMatrix (r.edge i)).IsHermitian) ∧ (complexMatrix r.effect).IsHermitian

def qEmbedSite {q L : ℕ} (A : QMatrix (Fin q)) (x : Site L) : QMatrix (Config q L) :=
  fun s t => if ∀ y, y ≠ x → s y = t y then A (s x) (t x) else 0

def qEmbedEdge {q L : ℕ} (A : QMatrix (Fin q × Fin q)) (x y : Site L) : QMatrix (Config q L) :=
  fun s t => if ∀ z, z ≠ x → z ≠ y → s z = t z then A (s x,s y) (t x,t y) else 0

def qHamiltonian {q : ℕ} (r : RationalTerms q) (L : ℕ) (phi : ℚ) : QMatrix (Config q L) :=
  (∑ x : Site L, qEmbedSite (r.onsite - qScale phi r.effect) x) +
  ∑ i : Fin 3, ∑ xy ∈ internalEdges L i, qEmbedEdge (r.edge i) xy.1 xy.2

def siteCode {L : ℕ} (x : Site L) : ℕ := (x 0).val + L*(x 1).val + L^2*(x 2).val

def decodeConfig {q : ℕ} (hq : 0 < q) (L : ℕ) (n : ℕ) : Config q L :=
  fun x => ⟨(n / q^(siteCode x)) % q, Nat.mod_lt _ hq⟩

/-- Real symmetric representation of a complex Hermitian matrix. The two
blocks duplicate each eigenvalue; the least eigenvalue is unchanged. -/
def realBlock {n : ℕ} (A : QMatrix (Fin n)) : Matrix (Fin (2*n)) (Fin (2*n)) ℚ :=
  fun i j =>
    if hi : i.val < n then
      if hj : j.val < n then (A ⟨i.val,hi⟩ ⟨j.val,hj⟩).re
      else -(A ⟨i.val,hi⟩ ⟨j.val-n,by omega⟩).im
    else
      if hj : j.val < n then (A ⟨i.val-n,by omega⟩ ⟨j.val,hj⟩).im
      else (A ⟨i.val-n,by omega⟩ ⟨j.val-n,by omega⟩).re

/-- A nonpositive pivot, including equality, rejects positive definiteness.
This is a finite exact rational recursion, not a promised spectral test. -/
def schurPositive : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → Bool
  | 0, _ => true
  | n+1, A => if 0 < A 0 0 then
      schurPositive n (fun i j => A i.succ j.succ - A i.succ 0*A 0 j.succ/A 0 0)
    else false

def bisectEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0, I => I
  | k+1, I =>
      let m := (I.1+I.2)/2
      bisectEnergy A k (if schurPositive n (A-m • (1 : Matrix (Fin n) (Fin n) ℚ))
        then (m,I.2) else (I.1,m))

def entryBound {n : Type} [Fintype n] (A : QMatrix n) : ℚ :=
  ∑ i : n, ∑ j : n, (|(A i j).re| + |(A i j).im|)

def termsBound {q : ℕ} (r : RationalTerms q) : ℚ :=
  1 + entryBound r.effect + entryBound r.onsite + ∑ i : Fin 3, entryBound (r.edge i)

/-- Dense rational matrix construction followed by Schur tests and bisection.
Fuel uses only rational input sizes and guarantees width at most 2*zeta. -/
def computedEnergy {q : ℕ} (hq : 0 < q) (r : RationalTerms q)
    (L : ℕ) (phi zeta : ℚ) : ℚ :=
  let D := q^(L^3)
  let X : QMatrix (Fin D) := fun i j =>
    qReal (1/(L : ℚ)^3) * qHamiltonian r L phi
      (decodeConfig hq L i.val) (decodeConfig hq L j.val)
  let A := realBlock X
  let G := termsBound r
  let fuel := 4*G.num.natAbs*zeta.den+4
  let I := bisectEnergy A fuel (-G,G)
  (I.1+I.2)/2

def energySide {q : ℕ} (p : FieldData q) (k : ℕ) : ℕ :=
  ⌈16*recoveryC p/(gap p*roundMargin k)⌉₊

def energyComparisons {q : ℕ} (hq : 0 < q) (p : FieldData q)
    (r : RationalTerms q) : ℕ → List Bool
  | 0 => []
  | k+1 =>
      let hst := energyComparisons hq p r k
      let phi := historyField hst k
      let h := roundMargin k/2
      let zeta := gap p*roundMargin k/32
      let L := energySide p k
      let s := -(computedEnergy hq r L (phi+h) zeta -
        computedEnergy hq r L (phi-h) zeta)/(2*h)
      hst ++ [decide ((p.a+p.b)/2 ≤ s)]

def energySearch {q : ℕ} (hq : 0 < q) (p : FieldData q)
    (r : RationalTerms q) (epsilon : ℚ) : ℚ :=
  groundOutput (energyComparisons hq p r (groundRounds epsilon))

/-- Exactly the preceding uniform bound (52); it concerns the reconstructed
rational interaction and the original canonical limiting energy. -/
def EnergyApproximation {q : ℕ} (p : FieldData q) (u : FieldInteraction q)
    (r : RationalTerms q) (Delta : ℝ) : Prop :=
  RationalHermitian r ∧ 0 ≤ Delta ∧ ∀ (L : ℕ), 1 ≤ L →
    ∀ phi ∈ Set.Icc (0 : ℝ) 1,
    |canonicalEnergy (complexTerms r) (complexMatrix r.effect) L phi -
      (fieldLimitEnergy p u phi - scalarShift u)| ≤ Delta + (recoveryC p : ℝ)/L

end GibbsTransition.SizeCopies.Supplement


