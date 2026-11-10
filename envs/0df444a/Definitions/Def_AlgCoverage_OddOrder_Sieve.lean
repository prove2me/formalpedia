-- Prove2me | Definitions.Def_AlgCoverage_OddOrder_Sieve
-- name    : AlgCoverage_OddOrder_Sieve
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:46:24.800368+00:00
-- url     : https://prove2.me/theorems/d62db48e-288e-48f3-bf55-e314e743a8e8
-- title:
--   The sieve objects of §8: event universe, active set, circuits, the family $K$, coefficients $a_i$, defect count $D_r$, and the parameters (8.2) and $\eta$
-- statement:
--   Fix a target set $B$ and inputs $x\in G^k$. The **event universe** is $E=(\{0,1\}^k\setminus\{0\})\times B$ with a fixed total order; an event $e=(v,b)$ is **active** when $W_v=b$, and $H\subseteq E$ is the **active set**. A **circuit** is a minimally FULL-failing subset $C\subseteq E$ with distinct masks (FULL of its masks fails, every proper subset passes); its **broken part** is $C\setminus\{\min C\}$. The family $K$ consists of the subsets of $E$ that contain neither a parallel pair (two events with the same mask and different targets) nor the broken part of a circuit. The coefficients are
--   $$a_i=\mathbb E\,\#\{I\subseteq H : I\in K,\ |I|=i\},\qquad a_0=1,$$
--   and for a cutoff $r$ the **defect count** $D_r$ counts the allowed active sets $I$ with $|I|\le r-1$, $a:=\min H\notin I$ and $I\cup\{a\}\notin K$; $D_r=0$ when $H$ is empty.
--
--   The parameters (8.2) are $n_2=\lfloor k/64\rfloor$, $n_1=k-n_2$, $\ell_1=\lfloor k/128\rfloor$, $\ell_2=n_2-\ell_1$, $\rho=B_*2^{n_2}(31/32)^{n_1}$, $\mu=mM/N$, $\nu=m2^k/N$ with $M=2^k-1$ and $m=|B|$, and
--   $$\eta=\max_{0\le i\le R}\Big\{\frac{4i^2}{M}+2\beta+4J(m+1)\rho4^i\Big\}.$$
--
--   **Formalization Note.** Events are pairs `(Fin k → Bool) × G`; the total order is a rank `ord`, assumed injective on $E$ in the statements ($e<e'$ iff `ord e < ord e'`). The broken part is the set of elements of $C$ that are not least. `FULLset` is FULL of the masks of a finite set of events. `coeffA` sets $a_0=1$ explicitly and uses the iid expectation otherwise. In `defectCount`, $|I|\le r-1$ is written $|I|+1\le r$, and the least active element is any $a\in H$ with minimal rank, which does not exist when $H=\varnothing$. Natural-number floors are `/`.
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), pp. 23–24 (PDF 24–25), §8 and §8.1; p. 24 (PDF 25), Eq. (8.2); p. 26 (PDF 27), Proposition 8.1

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage
import Definitions.Def_AlgCoverage_OddOrder_Series

namespace AlgCoverage.OddOrder

/-! The sieve objects of §8 (Lin, printed pp. 23–24 / PDF 24–25). An event is a pair `e = (v, b)` of
a mask `v ∈ {0,1}^k` and a target `b ∈ G`. The fixed total order on the event universe is given by a
rank `ord`, injective on the universe (`e < e' ↔ ord e < ord e'`). -/

/-- The event universe `E = ({0,1}^k \ {0}) × B`. -/
noncomputable def eventSet {G : Type*} [Group G] [Fintype G] (k : ℕ) (B : Finset G) :
    Finset ((Fin k → Bool) × G) := by
  classical
  exact Finset.univ.filter (fun e => e.1 ≠ (fun _ => false) ∧ e.2 ∈ B)

/-- The active set `H ⊆ E`: the events `e = (v, b)` with `W_v = b`. -/
noncomputable def activeSet {G : Type*} [Group G] [Fintype G] {k : ℕ} (B : Finset G)
    (x : Fin k → G) : Finset ((Fin k → Bool) × G) := by
  classical
  exact (eventSet k B).filter (fun e => word x e.1 = e.2)

/-- FULL of a finite set of events: FULL of the selector array formed by their masks. -/
def FULLset {G : Type*} [Group G] (s : NormalEASeries G) {k : ℕ} (x : Fin k → G)
    (I : Finset ((Fin k → Bool) × G)) : Prop :=
  FULL s x (fun e : I => e.1.1)

/-- A circuit: a minimally FULL-failing subset of `E` with distinct masks. -/
def IsCircuit {G : Type*} [Group G] [Fintype G] (s : NormalEASeries G) {k : ℕ} (B : Finset G)
    (x : Fin k → G) (C : Finset ((Fin k → Bool) × G)) : Prop :=
  C ⊆ eventSet k B ∧ Set.InjOn Prod.fst (C : Set ((Fin k → Bool) × G)) ∧
    ¬ FULLset s x C ∧ ∀ C' ⊂ C, FULLset s x C'

/-- The broken part `C \ {min C}` of a set of events (the elements that are not the least). -/
noncomputable def brokenPart {k : ℕ} {G : Type*} (ord : (Fin k → Bool) × G → ℕ)
    (C : Finset ((Fin k → Bool) × G)) : Finset ((Fin k → Bool) × G) := by
  classical
  exact C.filter (fun e => ∃ e' ∈ C, ord e' < ord e)

/-- Membership in the family `K`: a subset of `E` containing neither a parallel pair (same mask,
different target) nor the broken part of a circuit. -/
def Allowed {G : Type*} [Group G] [Fintype G] (s : NormalEASeries G) {k : ℕ} (B : Finset G)
    (ord : (Fin k → Bool) × G → ℕ) (x : Fin k → G) (I : Finset ((Fin k → Bool) × G)) : Prop :=
  I ⊆ eventSet k B ∧
    (¬ ∃ e ∈ I, ∃ e' ∈ I, e.1 = e'.1 ∧ e.2 ≠ e'.2) ∧
    ¬ ∃ C, IsCircuit s B x C ∧ brokenPart ord C ⊆ I

/-- `#{I ⊆ H : I ∈ K, |I| = i}` for fixed inputs. -/
noncomputable def allowedCount {G : Type*} [Group G] [Fintype G] (s : NormalEASeries G) {k : ℕ}
    (B : Finset G) (ord : (Fin k → Bool) × G → ℕ) (i : ℕ) (x : Fin k → G) : ℕ := by
  classical
  exact ((activeSet B x).powerset.filter (fun I => Allowed s B ord x I ∧ I.card = i)).card

/-- The coefficients `a_i = E #{I ⊆ H : I ∈ K, |I| = i}` (iid expectation), with `a_0 = 1`. -/
noncomputable def coeffA {G : Type*} [Group G] [Fintype G] (s : NormalEASeries G) (k : ℕ)
    (B : Finset G) (ord : (Fin k → Bool) × G → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 1 else expIid G k (fun x => (allowedCount s B ord i x : ℝ))

/-- The defect count `D_r`: the number of allowed active sets `I` with `|I| ≤ r − 1`, `a := min H ∉ I`
and `I ∪ {a} ∉ K`; it is `0` when `H` is empty (there is no least active element). -/
noncomputable def defectCount {G : Type*} [Group G] [Fintype G] (s : NormalEASeries G) {k : ℕ}
    (B : Finset G) (ord : (Fin k → Bool) × G → ℕ) (r : ℕ) (x : Fin k → G) : ℕ := by
  classical
  exact ((activeSet B x).powerset.filter (fun I =>
    Allowed s B ord x I ∧ I.card + 1 ≤ r ∧
      ∃ a ∈ activeSet B x, (∀ e ∈ activeSet B x, ord a ≤ ord e) ∧ a ∉ I ∧
        ¬ Allowed s B ord x (insert a I))).card

/-! Parameters (8.2) and the coefficient error `η` of Proposition 8.1. -/

/-- `n₂ = ⌊k/64⌋`. -/
def paramN2 (k : ℕ) : ℕ := k / 64
/-- `n₁ = k − n₂`. -/
def paramN1 (k : ℕ) : ℕ := k - paramN2 k
/-- `ℓ₁ = ⌊k/128⌋`. -/
def paramL1 (k : ℕ) : ℕ := k / 128
/-- `ℓ₂ = n₂ − ℓ₁`. -/
def paramL2 (k : ℕ) : ℕ := paramN2 k - paramL1 k

/-- `ρ = B_* 2^{n₂} (31/32)^{n₁}`. -/
noncomputable def paramRho (Bstar : ℝ) (k : ℕ) : ℝ :=
  Bstar * (2 : ℝ) ^ paramN2 k * (31 / 32 : ℝ) ^ paramN1 k

/-- `µ = m M / N` with `M = 2^k − 1`. -/
noncomputable def paramMu (m k N : ℕ) : ℝ := (m : ℝ) * ((2 : ℝ) ^ k - 1) / (N : ℝ)

/-- `ν = m 2^k / N`. -/
noncomputable def paramNu (m k N : ℕ) : ℝ := (m : ℝ) * (2 : ℝ) ^ k / (N : ℝ)

/-- `η = max_{0 ≤ i ≤ R} {4i²/M + 2β + 4J(m+1)ρ4^i}` with `M = 2^k − 1`. -/
noncomputable def paramEta (R k J m : ℕ) (β ρ : ℝ) : ℝ :=
  (Finset.range (R + 1)).sup' ⟨0, by simp⟩ (fun i =>
    4 * (i : ℝ) ^ 2 / ((2 : ℝ) ^ k - 1) + 2 * β + 4 * (J : ℝ) * ((m : ℝ) + 1) * ρ * (4 : ℝ) ^ i)

end AlgCoverage.OddOrder


