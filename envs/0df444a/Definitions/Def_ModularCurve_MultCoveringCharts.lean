-- Prove2me | Definitions.Def_ModularCurve_MultCoveringCharts
-- name    : ModularCurve_MultCoveringCharts
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/801a35d5-b344-503a-9a8b-76d95a69af96
-- title:
--   Two-chart covering context for X0​(p) and its statement
-- statement:
--   Fix a prime $p$ and a valuation subring $A\subseteq\overline{\mathbb Q}$ with residue field $k$ of characteristic $p$. The module first names the functions involved: `jF` and `jpF` are the elements of the level-$1\cdot p$ geometric modular function field given by the $q$-expansions of $j$ and of $j(q^p)$, `tieG` is $j(q^p)-j^p$, `jBar k` is the reduced $j$ inside `modularFunctionFieldC k 1`, `nCharts` is $2$, `modulusExp` is $3$, `mAnnuli p` is $\lfloor p/12\rfloor+[p\equiv2\ (3)]+[p\equiv3\ (4)]$, and `Fbar A i` is constantly the level-one geometric function field over $k$. `IsSSCentred A p W a` says that there are $x,y\in A$ with residues $a$ and $a^p$ such that $W$ has positive order at $j-x$ and at $j(q^p)-y$. `ChartCtx p A` bundles: modular polynomial data with its Kronecker congruence, two Hecke integrality hypotheses, a place specialization $P$ of $A$ at $p$ in level one, a level-one prolongation pair $R$ over $P$ (two regular prolongations exchanged by the Fricke involution, with compatible residue maps to `modularFunctionFieldC k 1`), a set $S_1$ of places of the level-$1\cdot p$ field, a finset `Wn` whose members are exactly the supersingular places `ssPlaces p 1 k`, witnesses that `ssJSet p k` (the $j$-invariants all of whose curves have trivial $p$-torsion) is finite of cardinality `mAnnuli p`, and a `ChartFstSupply` for $(R,S_1)$.
--
--   From such a context, `infChart` is the component chart `chartFst` (integers and residue from $R.R_1$, domain the strict type-one places together with the infinity-side places and $S_1$, nodes `Wn`, place map `P.redFst`), `zeroChart` is its pullback along the Fricke involution (same nodes, domain and integers transported), and `chart` indexes the pair; `src` and `tgt` are constantly $1$ and $0$. An enumeration `ssValue` identifies `Fin (mAnnuli p)` with the supersingular $j$-values (with injectivity, surjectivity and inverse `edgeOf`), and `nodeSrc`, `nodeTgt` are the geometric places at $a_e^{\,p}$ and $a_e$, the two members of `frobNodePair p a_e`; `ordBranch` is $S_1$.
--
--   `Statement p hp lvl hpl s`, for a family $s$ of elements of the level-$lvl$ field with $p\mid lvl$, asserts the existence of integers $n,m,B,k$ and a real $C$ with $m>0$ such that for every valuation subring $A$ over $p$ there are fields $\overline F_i$ over the residue field, component charts $C_i$, annuli $An_e, An'_e$ and edge data satisfying, as summarised conjuncts: paired annuli with equal domains and moduli and reciprocal parameters ($\mathrm{param}\cdot\mathrm{param}'=\mathrm{modulus}$); attachment of each annulus pair to the node places $xs_e$, $xt_e$; every node of every chart hit by some edge end, and uniquely so; the chart and annulus domains partitioning all places; the cusp $\infty$ lying in some chart, on which each $s_l$ becomes a unit residue after scaling by $c$ with $p^Bc, p^Bc^{-1}\in A$; principality of divisors and rationality of all places on each $\overline F_i$; connectedness of the chart graph; $p$ dividing each modulus and each modulus dividing $p^k$; for each chart a function $T_i$ whose translate by the value at a place has residue of order one and vanishes at that place only in its fibre; two nonarchimedean proximity estimates, bounding $|\mathrm{prox}|$ (the chordal proximity of the vectors $s(P)$, $s(Q)$) corrected by the $T_i$-distance, respectively plain, by $C\cdot(-\log\mu(p))$; and, for each supersingular $a\neq 0,1728$, an edge $e$ whose annulus parameter is $j(q^p)-j^p$ and whose two node places are centred at $a$ and $a^p$ in the sense of `IsSSCentred`. `StatementAll` quantifies this over all families $s$ satisfying `IsEmbBasis lvl s`, and `StatementAll_congr` transports it along an equality of levels.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here (valuation subrings, residue fields of local rings, absolute values, `Relation.ReflTransGen`); component charts, annuli on a curve, the chordal proximity function `prox`, modular function fields of this shape and place specializations are the project's own.
--
--   **Where it is used.** These definitions fix the bookkeeping for the two-component semistable covering of $X_0(p)$ over a valuation ring above $p$ — the two charts corresponding to the components of the special fibre, joined along annuli at the supersingular points — and package the covering, together with its $p$-adic proximity estimates for an embedding basis, as a single proposition in the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_MultCoveringCharts.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_ModularCurve_LevelOneChartFst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve.MultCovering

section Instances
variable (A : ValuationSubring (AlgebraicClosure ℚ))

instance instFieldFbar : Field ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) := inferInstance

instance instAlgebraFbar :
    Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  inferInstance

end Instances

abbrev jF (p : ℕ) [Fact p.Prime] : modularFunctionFieldBar (1 * p) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩

abbrev jpF (p : ℕ) [Fact p.Prime] : modularFunctionFieldBar (1 * p) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_mul_left p 1))⟩

abbrev tieG (p : ℕ) [Fact p.Prime] : modularFunctionFieldBar (1 * p) := jpF p - jF p ^ p

theorem jF_eq_jFun (p : ℕ) [Fact p.Prime] : jF p = PlaceSpecialization.jFun (q := p) := rfl

abbrev jBar (k : Type) [Field k] : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩

abbrev nCharts : ℕ := 2

def mAnnuli (p : ℕ) : ℕ := p / 12 + (if p % 3 = 2 then 1 else 0) + (if p % 4 = 3 then 1 else 0)

def modulusExp : ℕ := 3

abbrev Fbar (A : ValuationSubring (AlgebraicClosure ℚ)) (_i : Fin nCharts) : Type :=
  ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)

abbrev IsSSCentred (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (a : IsLocalRing.ResidueField ↥A) : Prop :=
  ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsSSCentred A p W a

structure ChartCtx (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] where
  data  : ModularPolynomialData p
  hKr   : KroneckerCongruence p data
  hα    : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p
  hβ    : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p
  P     : PlaceSpecialization A p 1 data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ
  R     : P.LevelOneProlongationPair

  S₁    : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))

  Wn    : Finset (Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
  hWn   : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (IsLocalRing.ResidueField ↥A)

  hfin  : (ssJSet p (IsLocalRing.ResidueField ↥A)).Finite
  hcard : hfin.toFinset.card = mAnnuli p

  supply : R.ChartFstSupply S₁

section PerA

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

def infChart :
    ComponentChart A ↥(modularFunctionFieldBar (1 * p)) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply

def zeroChart :
    ComponentChart A ↥(modularFunctionFieldBar (1 * p)) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  (infChart Γ).comap (frickeInvolutionBar (1 * p))

def chart (i : Fin nCharts) : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) (Fbar A i) :=
  ![infChart Γ, zeroChart Γ] i

@[simp] theorem chart_zero : chart Γ 0 = infChart Γ := rfl
@[simp] theorem chart_one : chart Γ 1 = zeroChart Γ := rfl

def src (p : ℕ) (_e : Fin (mAnnuli p)) : Fin nCharts := 1

def tgt (p : ℕ) (_e : Fin (mAnnuli p)) : Fin nCharts := 0

def ssValue (e : Fin (mAnnuli p)) : IsLocalRing.ResidueField ↥A :=
  ((Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard).symm e : ↥Γ.hfin.toFinset)

theorem ssValue_mem_toFinset (e : Fin (mAnnuli p)) : ssValue Γ e ∈ Γ.hfin.toFinset :=
  ((Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard).symm e).2

theorem ssValue_mem_ssJSet (e : Fin (mAnnuli p)) : ssValue Γ e ∈ ssJSet p (IsLocalRing.ResidueField ↥A) :=
  Γ.hfin.mem_toFinset.mp (ssValue_mem_toFinset Γ e)

theorem ssValue_injective : Function.Injective (ssValue Γ) := fun _ _ h =>
  (Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard).symm.injective (Subtype.ext h)

theorem exists_ssValue_eq (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ∃ e, ssValue Γ e = a :=
  ⟨Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard ⟨a, Γ.hfin.mem_toFinset.mpr ha⟩, by simp [ssValue]⟩

def edgeOf (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) : Fin (mAnnuli p) :=
  Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard ⟨a, Γ.hfin.mem_toFinset.mpr ha⟩

@[simp] theorem ssValue_edgeOf (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ssValue Γ (edgeOf Γ a ha) = a := by
  simp [ssValue, edgeOf]

def nodeSrc (e : Fin (mAnnuli p)) : Place (IsLocalRing.ResidueField ↥A) (Fbar A (src p e)) :=
  charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e ^ p)

def nodeTgt (e : Fin (mAnnuli p)) : Place (IsLocalRing.ResidueField ↥A) (Fbar A (tgt p e)) :=
  charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)

theorem nodeSrc_eq (e : Fin (mAnnuli p)) : nodeSrc Γ e = (frobNodePair p (ssValue Γ e)).2 := rfl
theorem nodeTgt_eq (e : Fin (mAnnuli p)) : nodeTgt Γ e = (frobNodePair p (ssValue Γ e)).1 := rfl

def ordBranch : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) := Γ.S₁

end PerA

def Statement (p : ℕ) (hp : p.Prime) (lvl : ℕ) [NeZero lvl] (hpl : p ∣ lvl) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar lvl) : Prop :=
    ∃ (n m B k : ℕ) (Cc : ℝ), 0 < m ∧ ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ [DecidableEq (IsLocalRing.ResidueField ↥A)],
    ∃ (Fbar : Fin n → Type) (_ : ∀ i, Field (Fbar i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField ↥A) (Fbar i))
      (C : ∀ i, ComponentChart A (modularFunctionFieldBar lvl) (Fbar i))
      (An An' : Fin m → Annulus A (modularFunctionFieldBar lvl)) (src tgt : Fin m → Fin n)
      (xs : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (src e)))
      (xt : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (tgt e)))
      (T : ∀ i, Place (IsLocalRing.ResidueField ↥A) (Fbar i) → modularFunctionFieldBar lvl),
      (∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
        ((An e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (An' e).param * (An e).param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) ((An e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E') ∧
      (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl),
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
        (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)) ∧
      (∃ i, cuspInftyBar lvl ∈ (C i).dom ∧
        ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
          (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ (C i).integers, (C i).residue ⟨c • s l, h⟩ ≠ 0) ∧
      (∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar i) ∧
        ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar i), x.IsRational) ∧
      (∀ i j : Fin n, Relation.ReflTransGen
        (fun a b : Fin n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ k = ((An e).modulus : AlgebraicClosure ℚ) * a) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * a) ∧
      (∀ i, ∀ P ∈ (C i).dom,
        ∃ h : T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))
              ∈ (C i).integers,
          (C i).residue ⟨_, h⟩ ≠ 0 ∧ ((C i).placeMap P).ord ((C i).residue ⟨_, h⟩) = 1 ∧
          0 < P.ord (T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))) ∧
          ∀ Q ∈ (C i).dom, (C i).placeMap Q = (C i).placeMap P → Q ≠ P →
            Q.ord (T i ((C i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))) = 0) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i, ∀ P ∈ (C i).dom, ∀ Q ∈ (C i).dom, P ≠ Q →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          ((C i).placeMap P = (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (T i ((C i).placeMap P)) - Q.evalAt (T i ((C i).placeMap P))))|
              ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
          ((C i).placeMap P ≠ (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl),
          (∀ i, P ∈ (C i).dom → Q ∉ (C i).dom) → (∀ e, P ∈ (An e).dom → Q ∉ (An e).dom) →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
      (letI : NeZero p := ⟨hp.ne_zero⟩;
       ∀ a : IsLocalRing.ResidueField ↥A, a ∈ ssJSet p (IsLocalRing.ResidueField ↥A) →
        a ≠ 0 → a ≠ 1728 → ∃ e,
        (An e).param
          = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full lvl hpl)⟩ :
                modularFunctionFieldBar lvl)
            - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full lvl (jq_mem lvl))⟩ : modularFunctionFieldBar lvl) ^ p ∧
        (∃ xl : A, IsLocalRing.residue ↥A xl = a ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full lvl (jq_mem lvl))⟩ : modularFunctionFieldBar lvl)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (xl : AlgebraicClosure ℚ)
              ∈ (C (src e)).integers,
            0 < (xs e).ord ((C (src e)).residue ⟨_, h⟩)) ∧
        (∃ yl : A, IsLocalRing.residue ↥A yl = a ^ p ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full lvl hpl)⟩ :
                modularFunctionFieldBar lvl)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (yl : AlgebraicClosure ℚ)
              ∈ (C (tgt e)).integers,
            0 < (xt e).ord ((C (tgt e)).residue ⟨_, h⟩)))

def StatementAll (p : ℕ) (hp : p.Prime) (lvl : ℕ) [NeZero lvl] (hpl : p ∣ lvl) : Prop :=
  ∀ {r : ℕ} (s : Fin r → modularFunctionFieldBar lvl), IsEmbBasis lvl s → Statement p hp lvl hpl s

theorem StatementAll_congr (p : ℕ) (hp : p.Prime) {l₁ l₂ : ℕ} [NeZero l₁] [NeZero l₂] (h : l₁ = l₂)
    (h₁ : p ∣ l₁) (h₂ : p ∣ l₂) : StatementAll p hp l₁ h₁ → StatementAll p hp l₂ h₂ := by
  subst h
  exact id

end ModularCurve.MultCovering

end


