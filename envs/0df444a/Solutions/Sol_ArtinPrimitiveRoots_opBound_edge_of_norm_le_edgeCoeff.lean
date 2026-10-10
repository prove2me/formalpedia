-- Prove2me | solution 1 for ArtinPrimitiveRoots.opBound_edge_of_norm_le_edgeCoeff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:28:04.508994+00:00
-- url     : https://prove2.me/submissions/d4c340b6-56fa-44d8-84ab-2eb37cd1cc3e

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinMemoryModel
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare

section
/-! # L102D_OpDefs — alias of the bundle `Def_ArtinMinorOperator` (round 5)

The operator model now lives in `Definitions/Def_ArtinMinorOperator.lean` (same declarations, same
names). This module re-exports it and keeps `listProd`, which only the proofs use. -/

namespace ArtinPrimitiveRoots

end ArtinPrimitiveRoots
end

section
/-! # L102D_MemDefs — alias of the bundle `Def_ArtinMemoryModel` (round 5)

The memory model (root coordinates, `pathPhi`, `rootIL`, the memory space, `ghostOp`, `edgeOp`,
`memMomentD`, `dyadParams`, and `MemParams.RootIn`) now lives in
`Definitions/Def_ArtinMemoryModel.lean` (same declarations, same names). -/
end

section
/-! # L102G: the Hilbert-space framework for the edge bound (D7d)

On `H_B = ℓ²(stSet, μ)`, `μ = stWeight`:

* `ipμ g h = Σ_s μ(s) conj(g s) h s`; `opBound_of_bilin`: a bilinear bound gives `OpBound`;
* slot permutations `permS`; `μ` and `stSet` are invariant (`stWeight_permS`, `sum_permS`);
* `symM` is self-adjoint (`ipμ_symM`), a contraction (`wNorm_symM_le`), and its images are
  symmetric (`symM_permS`); `sum_sym_avg` replaces a row sum by its permutation average;
* `ipμ_edgeOp`: `⟨g, E f⟩ = ⟨Sg, E^ord Sf⟩`;
* `piece_bound`: the Cauchy–Schwarz/Schur bound for one piece of a choice-indexed operator.
-/

namespace ArtinPrimitiveRoots.L102G

open Real Finset
open scoped ComplexConjugate

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-! ## The weighted inner product -/

/-- `⟨g, h⟩_μ = Σ_s μ(s) conj(g s) h s`. -/
noncomputable def ipμ (g h : P.MState → ℂ) : ℂ :=
  ∑ s ∈ P.stSet, (P.stWeight s : ℂ) * (conj (g s) * h s)

lemma ipμ_self (h : P.MState → ℂ) :
    ipμ P h h = ((∑ s ∈ P.stSet, P.stWeight s * ‖h s‖ ^ 2 : ℝ) : ℂ) := by
  unfold ipμ
  push_cast
  refine sum_congr rfl fun s _ => ?_
  rw [mul_comm (conj (h s)), Complex.mul_conj']

/-- A bilinear bound gives the operator bound. -/
theorem opBound_of_bilin (O : (P.MState → ℂ) → (P.MState → ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s)
    (h : ∀ g f, ‖ipμ P g (O f)‖ ≤ C * P.wNorm g * P.wNorm f) : P.OpBound (O) C := by
  intro f
  have hsq : ∀ u : P.MState → ℂ, P.wNorm u ^ 2 = ∑ s ∈ P.stSet, P.stWeight s * ‖u s‖ ^ 2 :=
    fun u => Real.sq_sqrt (sum_nonneg fun s hs => mul_nonneg (hμ s hs) (sq_nonneg _))
  have h1 := h (O f) f
  rw [ipμ_self, Complex.norm_real, Real.norm_of_nonneg
    (sum_nonneg fun s hs => mul_nonneg (hμ s hs) (sq_nonneg _)), ← hsq] at h1
  have hn : 0 ≤ P.wNorm (O f) := Real.sqrt_nonneg _
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg hC (Real.sqrt_nonneg _)
  · have : P.wNorm (O f) * P.wNorm (O f) ≤ (C * P.wNorm f) * P.wNorm (O f) := by
      nlinarith
    exact le_of_mul_le_mul_right this hpos

/-! ## The slot symmetrization -/

/-! ## One piece of a choice-indexed operator -/

variable {γ : Type*}

/-- Cauchy–Schwarz for a piece: rows against `G`, columns against `F`. -/
theorem piece_bound (Ch : Finset γ) (coeffP : P.MState → γ → ℂ) (out : P.MState → γ → P.MState)
    (G F : P.MState → ℂ) (R C : ℝ) (hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s)
    (hrow : ∑ s ∈ P.stSet, ∑ c ∈ Ch, P.stWeight s * ‖coeffP s c‖ *
      (if out s c ∈ P.stSet then 1 else 0) * ‖G s‖ ^ 2 ≤
        R * ∑ s ∈ P.stSet, P.stWeight s * ‖G s‖ ^ 2)
    (hcol : ∑ s ∈ P.stSet, ∑ c ∈ Ch, P.stWeight s * ‖coeffP s c‖ *
      (if out s c ∈ P.stSet then ‖F (out s c)‖ ^ 2 else 0) ≤
        C * ∑ s ∈ P.stSet, P.stWeight s * ‖F s‖ ^ 2) :
    ‖∑ s ∈ P.stSet, (P.stWeight s : ℂ) * (conj (G s) * ∑ c ∈ Ch, coeffP s c *
      (if out s c ∈ P.stSet then F (out s c) else 0))‖ ≤ √R * √C * P.wNorm G * P.wNorm F := by
  set W : P.MState × γ → ℝ := fun q => P.stWeight q.1 * ‖coeffP q.1 q.2‖ *
    (if out q.1 q.2 ∈ P.stSet then 1 else 0)
  have hW : ∀ q ∈ P.stSet ×ˢ Ch, 0 ≤ W q := by
    intro q hq
    simp only [W]
    have := hμ q.1 (mem_product.1 hq).1
    split_ifs <;> positivity
  have h1 : ‖∑ s ∈ P.stSet, (P.stWeight s : ℂ) * (conj (G s) * ∑ c ∈ Ch, coeffP s c *
      (if out s c ∈ P.stSet then F (out s c) else 0))‖ ≤
      ∑ q ∈ P.stSet ×ˢ Ch, (√(W q) * ‖G q.1‖) * (√(W q) *
        (if out q.1 q.2 ∈ P.stSet then ‖F (out q.1 q.2)‖ else 0)) := by
    rw [sum_product]
    refine (norm_sum_le _ _).trans (sum_le_sum fun s hs => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ s hs), Complex.norm_conj]
    calc P.stWeight s * (‖G s‖ * ‖∑ c ∈ Ch, coeffP s c *
          (if out s c ∈ P.stSet then F (out s c) else 0)‖) ≤
        P.stWeight s * (‖G s‖ * ∑ c ∈ Ch, ‖coeffP s c *
          (if out s c ∈ P.stSet then F (out s c) else 0)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sum_le _ _)
            (norm_nonneg _)) (hμ s hs)
      _ = _ := by
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun c hc => ?_
          have hWq := hW (s, c) (mem_product.2 ⟨hs, hc⟩)
          rw [show √(W (s, c)) * ‖G (s, c).1‖ * (√(W (s, c)) *
              (if out (s, c).1 (s, c).2 ∈ P.stSet then ‖F (out (s, c).1 (s, c).2)‖ else 0)) =
              (√(W (s, c)) * √(W (s, c))) * ‖G s‖ *
                (if out s c ∈ P.stSet then ‖F (out s c)‖ else 0) by ring,
            Real.mul_self_sqrt hWq]
          simp only [W]
          by_cases ho : out s c ∈ P.stSet
          · simp only [if_pos ho, norm_mul]; ring
          · simp only [if_neg ho, norm_mul, norm_zero]; ring
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (P.stSet ×ˢ Ch) (fun q => √(W q) * ‖G q.1‖)
    (fun q => √(W q) * (if out q.1 q.2 ∈ P.stSet then ‖F (out q.1 q.2)‖ else 0))
  have h3 : ∑ q ∈ P.stSet ×ˢ Ch, (√(W q) * ‖G q.1‖) ^ 2 ≤
      R * ∑ s ∈ P.stSet, P.stWeight s * ‖G s‖ ^ 2 := by
    refine le_trans (le_of_eq ?_) hrow
    rw [sum_product]
    refine sum_congr rfl fun s hs => sum_congr rfl fun c hc => ?_
    rw [mul_pow, Real.sq_sqrt (hW (s, c) (mem_product.2 ⟨hs, hc⟩))]
  have h4 : ∑ q ∈ P.stSet ×ˢ Ch, (√(W q) *
      (if out q.1 q.2 ∈ P.stSet then ‖F (out q.1 q.2)‖ else 0)) ^ 2 ≤
      C * ∑ s ∈ P.stSet, P.stWeight s * ‖F s‖ ^ 2 := by
    refine le_trans (le_of_eq ?_) hcol
    rw [sum_product]
    refine sum_congr rfl fun s hs => sum_congr rfl fun c hc => ?_
    rw [mul_pow, Real.sq_sqrt (hW (s, c) (mem_product.2 ⟨hs, hc⟩))]
    simp only [W]
    split_ifs <;> simp
  have hG := sum_nonneg fun s hs => mul_nonneg (hμ s hs) (sq_nonneg ‖G s‖)
  have hF := sum_nonneg fun s hs => mul_nonneg (hμ s hs) (sq_nonneg ‖F s‖)
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ √(R * ∑ s ∈ P.stSet, P.stWeight s * ‖G s‖ ^ 2) *
        √(C * ∑ s ∈ P.stSet, P.stWeight s * ‖F s‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt h3) (Real.sqrt_le_sqrt h4) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = √R * √C * P.wNorm G * P.wNorm F := by
        unfold MemParams.wNorm
        rw [Real.sqrt_mul' _ hG, Real.sqrt_mul' _ hF]; ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: reversing an edge (columns are rows of the reversed edge)

For a choice `c = (St, z', tg)` at a state `s = (z, ℓ, m)` with output `s' = (z', ℓ', m')`, the
reversed choice at `s'` is `(I, z, (ℓᵢ(last), i ∈ St))`, `I` the promoted groups: promotions become
stores and stores become promotions. `rev_rev`: reversing twice is the identity;
`edgeOut_rev`: the reversed edge returns to `s`; `econd_rev`: it satisfies the edge conditions;
`weight_rev`: `μ(s) rfac(s,c) ∏_{I} Vᵢ = μ(s') rfac(s',c') ∏_{St} Vᵢ` (the Fock measure identity
`memW(m₀ + δ_y) (m₀(y) + 1) = memW(m₀) λ(y)`, [21] (4.18)). -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- Edge choices. -/
abbrev EC := Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)

/-! ## Lists -/

lemma newList_last (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K) :
    P.newList ℓ nw i (Fin.last P.J) = nw i := by
  simp [MemParams.newList]

lemma newList_castSucc (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K) (k : Fin P.J) :
    P.newList ℓ nw i k.castSucc = ℓ i k.castSucc := by
  simp [MemParams.newList]

lemma newList_newList (ℓ : P.Lst) (nw lab : Fin P.K → ℕ) :
    P.newList (P.newList ℓ nw) lab = P.newList ℓ lab := by
  funext i k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp [newList_last]
  · simp [newList_castSucc]

lemma newList_self (ℓ : P.Lst) : P.newList ℓ (fun i => ℓ i (Fin.last P.J)) = ℓ := by
  funext i k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp [newList_last]
  · simp [newList_castSucc]

lemma padProd_newList (ℓ : P.Lst) (nw : Fin P.K → ℕ) : padProd (P.newList ℓ nw) = padProd ℓ := by
  unfold padProd; simp only [newList_castSucc]

lemma lastProd_newList (ℓ : P.Lst) (nw : Fin P.K → ℕ) :
    lastProd (P.newList ℓ nw) = ∏ i, nw i := by
  unfold lastProd; simp only [newList_last]

lemma detZ_swap (z z' : ℤ × ℤ) : detZ z' z = -detZ z z' := by unfold detZ; ring

lemma newList_injective (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K)
    (hinj : Function.Injective (ℓ i)) (hban : nw i ∉ Set.range (ℓ i)) :
    Function.Injective (P.newList ℓ nw i) := by
  intro k k' h
  induction k using Fin.lastCases with
  | last =>
    induction k' using Fin.lastCases with
    | last => rfl
    | cast k' =>
      rw [newList_last, newList_castSucc] at h
      exact absurd ⟨_, h.symm⟩ hban
  | cast k =>
    induction k' using Fin.lastCases with
    | last =>
      rw [newList_last, newList_castSucc] at h
      exact absurd ⟨_, h⟩ hban
    | cast k' =>
      rw [newList_castSucc, newList_castSucc] at h
      exact congrArg _ (Fin.castSucc_injective _ (hinj h))

/-- The listed weight splits into pads and last labels. -/
lemma listWeight_newList_mul (ℓ : P.Lst) (nw : Fin P.K → ℕ) :
    P.listWeight ℓ * ∏ i, P.nu i (nw i) =
      P.listWeight (P.newList ℓ nw) * ∏ i, P.nu i (ℓ i (Fin.last P.J)) := by
  unfold MemParams.listWeight
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [newList_castSucc, newList_last]
  ring

/-! ## The edge condition and the real factor -/

/-- The condition of `edgeCoeff`. -/
def ECond (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) : Prop :=
  P.EdgeOK ω s.1 c.2.1 s.2.1 (fun i => (c.2.2 i).1) ∧
    (∀ i, (c.2.2 i).2 → P.promPart c.2.1 c.2.2 i ∈ P.partSet) ∧
    (∀ i ∈ c.1, P.storedPart s.1 s.2.1 i ∈ P.partSet) ∧
    (∀ y, P.promCount c.2.1 c.2.2 y ≤ s.2.2 y)

/-- The real factor of `edgeCoeff` (pending hits, promotions or fresh labels). -/
noncomputable def rfac (s : P.MState) (c : EC P) : ℝ :=
  memRho ^ P.hitCount s.1 s.2.2 *
    (∏ i, if (c.2.2 i).2 then (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i
      else P.nu i (c.2.2 i).1) *
    memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c)

open Classical in
/-- The edge coefficient with the geometric multiplier replaced by `κ t a b D`. -/
noncomputable def coeffK (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) : ℂ :=
  if ECond P ω s c then (rfac P s c : ℂ) *
    κ (detZ s.1 c.2.1 / padProd s.2.1) (∏ i, (c.2.2 i).1) (lastProd s.2.1) (padProd s.2.1) else 0

lemma edgeCoeff_eq (ω : ℝ × ℝ × ℝ) (j : ℕ) (s : P.MState) (c : EC P) :
    P.edgeCoeff ω j s c = coeffK P (P.edgeMult j) ω s c := by
  unfold MemParams.edgeCoeff coeffK ECond rfac
  congr 1

/-! ## The reversal -/

/-- The promoted groups. -/
def promSet (c : EC P) : Finset (Fin P.K) := univ.filter fun i => (c.2.2 i).2 = true

/-- The reversed choice. -/
def revC (s : P.MState) (c : EC P) : EC P :=
  (promSet P c, s.1, fun i => (s.2.1 i (Fin.last P.J), decide (i ∈ c.1)))

lemma storedPart_out (s : P.MState) (c : EC P) (i : Fin P.K) :
    P.storedPart (P.edgeOut s c).1 (P.edgeOut s c).2.1 i = P.promPart c.2.1 c.2.2 i := by
  simp only [MemParams.storedPart, MemParams.edgeOut, MemParams.promPart, newList_last]

lemma promCount_revC (s : P.MState) (c : EC P) (y : P.PT) :
    P.promCount s.1 (revC P s c).2.2 y = P.storeCount s.1 s.2.1 c.1 y := by
  unfold MemParams.promCount MemParams.storeCount
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, revC, decide_eq_true_eq]
  exact Iff.rfl

lemma storeCount_out (s : P.MState) (c : EC P) (y : P.PT) :
    P.storeCount (P.edgeOut s c).1 (P.edgeOut s c).2.1 (promSet P c) y =
      P.promCount c.2.1 c.2.2 y := by
  unfold MemParams.promCount MemParams.storeCount
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, promSet, storedPart_out]

lemma edgeOutMem_rev (s : P.MState) (c : EC P) (hc : ∀ y, P.promCount c.2.1 c.2.2 y ≤ s.2.2 y) :
    P.edgeOutMem (P.edgeOut s c) (revC P s c) = s.2.2 := by
  funext y
  unfold MemParams.edgeOutMem
  have h1 : (P.edgeOut s c).1 = c.2.1 := rfl
  have h2 := storeCount_out P s c y
  have h3 : (revC P s c).1 = promSet P c := rfl
  have h4 := promCount_revC P s c y
  have h5 : (P.edgeOut s c).2.2 y =
      s.2.2 y - P.promCount c.2.1 c.2.2 y + P.storeCount s.1 s.2.1 c.1 y := rfl
  have h6 : (revC P s c).2.1 = s.1 := rfl
  rw [h3, h2, h6, h4, h5]
  have := hc y
  omega

lemma edgeOut_rev (s : P.MState) (c : EC P) (hc : ∀ y, P.promCount c.2.1 c.2.2 y ≤ s.2.2 y) :
    P.edgeOut (P.edgeOut s c) (revC P s c) = s := by
  rcases s with ⟨z, ℓ, m⟩
  have hm := edgeOutMem_rev P (z, ℓ, m) c hc
  simp only [MemParams.edgeOut] at hm ⊢
  rw [hm]
  simp only [revC, newList_newList, newList_self]

lemma revC_rev (s : P.MState) (c : EC P) (hc : ∀ y, P.promCount c.2.1 c.2.2 y ≤ s.2.2 y) :
    revC P (P.edgeOut s c) (revC P s c) = c := by
  rcases c with ⟨St, z', tg⟩
  simp only [revC, promSet, MemParams.edgeOut, newList_last, mem_filter, mem_univ, true_and,
    decide_eq_true_eq]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · ext i; simp
  · funext i; simp

lemma ecLabels_rev (s : P.MState) (c : EC P) :
    (fun i => ((revC P s c).2.2 i).1) = fun i => s.2.1 i (Fin.last P.J) := rfl

lemma prod_labels_rev (s : P.MState) (c : EC P) :
    ∏ i, ((revC P s c).2.2 i).1 = lastProd s.2.1 := rfl

lemma lastProd_out (s : P.MState) (c : EC P) :
    lastProd (P.edgeOut s c).2.1 = ∏ i, (c.2.2 i).1 := by
  simp only [MemParams.edgeOut, lastProd_newList]

lemma padProd_out (s : P.MState) (c : EC P) :
    padProd (P.edgeOut s c).2.1 = padProd s.2.1 := by
  simp only [MemParams.edgeOut, padProd_newList]

lemma det_rev (s : P.MState) (c : EC P) (hD : (padProd s.2.1 : ℤ) ∣ detZ s.1 c.2.1) :
    detZ (P.edgeOut s c).1 (revC P s c).2.1 / padProd (P.edgeOut s c).2.1 =
      -(detZ s.1 c.2.1 / padProd s.2.1) := by
  rw [padProd_out]
  show detZ c.2.1 s.1 / _ = _
  rw [detZ_swap, Int.neg_ediv_of_dvd hD]

lemma econd_rev (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) (h : ECond P ω s c) :
    ECond P ω (P.edgeOut s c) (revC P s c) := by
  obtain ⟨⟨hinj, hban, hd1, hd2, hdvd, hb1, hb2, hg1, hg2⟩, hpp, hsp, hpc⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hb2, hb1, hg2, ?_⟩, ?_, ?_, ?_⟩
  · intro i; exact newList_injective P _ (fun i => (c.2.2 i).1) i (hinj i) (hban i)
  · intro i hi
    obtain ⟨k, hk⟩ := hi
    simp only [revC] at hk
    induction k using Fin.lastCases with
    | last =>
      simp only [MemParams.edgeOut, newList_last] at hk
      exact hban i ⟨_, hk.symm⟩
    | cast k =>
      simp only [MemParams.edgeOut, newList_castSucc] at hk
      exact absurd (hinj i hk) (Fin.castSucc_ne_last k)
  · rw [padProd_out]; exact hd1
  · rw [padProd_out]; exact hd2
  · rw [padProd_out]; show _ ∣ detZ c.2.1 s.1
    rw [detZ_swap]; exact (dvd_neg).2 hdvd
  · show P.GoodAt ω s.1 (P.newList (P.newList s.2.1 _) _)
    rw [newList_newList, ecLabels_rev, newList_self]; exact hg1
  · intro i hi
    simp only [revC, decide_eq_true_eq] at hi
    exact hsp i hi
  · intro i hi
    simp only [revC, promSet, mem_filter, mem_univ, true_and] at hi
    rw [storedPart_out]; exact hpp i hi
  · intro y
    show P.promCount s.1 (revC P s c).2.2 y ≤ _
    rw [promCount_revC]
    show P.storeCount s.1 s.2.1 c.1 y ≤
      s.2.2 y - P.promCount c.2.1 c.2.2 y + P.storeCount s.1 s.2.1 c.1 y
    omega

/-! ## The Fock measure identity -/

lemma memWeight_update (m : P.Mem) (y : P.PT) :
    P.memWeight (Function.update m y (m y + 1)) * ((m y : ℝ) + 1) = P.memWeight m * P.lam y := by
  unfold MemParams.memWeight
  rw [← mul_prod_erase univ _ (mem_univ y), ← mul_prod_erase univ _ (mem_univ y)]
  have h : ∏ x ∈ univ.erase y, P.lam x ^ Function.update m y (m y + 1) x /
      ((Function.update m y (m y + 1) x).factorial : ℝ) =
      ∏ x ∈ univ.erase y, P.lam x ^ m x / ((m x).factorial : ℝ) := by
    refine prod_congr rfl fun x hx => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hx)]
  rw [h, Function.update_self, Nat.factorial_succ]
  have hf : ((m y).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  push_cast
  field_simp
  ring

/-- The count of a family of particles indexed by `T`. -/
def cntF (T : Finset (Fin P.K)) (yf : Fin P.K → Fin P.K × ℕ × ℕ) : P.Mem :=
  fun y => (T.filter fun i => yf i = y.1).card

lemma memAt_of_mem (m : P.Mem) (y : Fin P.K × ℕ × ℕ) (h : y ∈ P.partSet) :
    P.memAt m y = m ⟨y, h⟩ := by
  unfold MemParams.memAt; rw [dif_pos h]

/-- **The Fock identity**: inserting the particles `yf i`, `i ∈ T` (one per group), and paying
their indexed counts is the same as paying their measures. -/
lemma fock_prod (T : Finset (Fin P.K)) (yf : Fin P.K → Fin P.K × ℕ × ℕ)
    (hyf1 : ∀ i, (yf i).1 = i) (hyp : ∀ i ∈ T, yf i ∈ P.partSet) (m₀ : P.Mem) :
    P.memWeight (m₀ + cntF P T yf) * ∏ i ∈ T, (P.memAt (m₀ + cntF P T yf) (yf i) : ℝ) =
      P.memWeight m₀ * ∏ i ∈ T, P.nu i (yf i).2.1 := by
  induction T using Finset.induction_on with
  | empty =>
    have : m₀ + cntF P ∅ yf = m₀ := by funext y; simp [cntF]
    rw [this]; simp
  | insert i T hi ih =>
    have hyi : yf i ∈ P.partSet := hyp i (mem_insert_self i T)
    have hyT : ∀ i' ∈ T, yf i' ∈ P.partSet := fun i' h => hyp i' (mem_insert_of_mem h)
    set y : P.PT := ⟨yf i, hyi⟩
    set mT := m₀ + cntF P T yf
    have hupd : m₀ + cntF P (insert i T) yf = Function.update mT y (mT y + 1) := by
      funext y'
      by_cases hy : y' = y
      · subst hy
        rw [Function.update_self]
        simp only [mT, Pi.add_apply, cntF, filter_insert]
        rw [if_pos (rfl : yf i = (y : Fin P.K × ℕ × ℕ)),
          card_insert_of_notMem (fun h => hi (mem_filter.1 h).1)]
        ring
      · rw [Function.update_of_ne hy]
        simp only [mT, Pi.add_apply, cntF, filter_insert]
        have : ¬ yf i = y'.1 := fun h => hy (Subtype.ext h.symm)
        rw [if_neg this]
    have hT : ∀ i' ∈ T, P.memAt (m₀ + cntF P (insert i T) yf) (yf i') = P.memAt mT (yf i') := by
      intro i' hi'
      rw [memAt_of_mem P _ _ (hyT i' hi'), memAt_of_mem P _ _ (hyT i' hi'), hupd]
      have : (⟨yf i', hyT i' hi'⟩ : P.PT) ≠ y := by
        intro h
        have := congrArg (fun q : P.PT => q.1.1) h
        simp only [y, hyf1] at this
        exact hi (this ▸ hi')
      rw [Function.update_of_ne this]
    rw [prod_insert hi, prod_insert hi, prod_congr rfl fun i' hi' => by rw [hT i' hi']]
    rw [memAt_of_mem P _ _ hyi, hupd, Function.update_self]
    have hw := memWeight_update P mT y
    have hlam : P.lam y = P.nu i (yf i).2.1 := by
      simp only [MemParams.lam, y, hyf1]
    push_cast
    calc P.memWeight (Function.update mT y (mT y + 1)) * (((mT y : ℝ) + 1) *
          ∏ i' ∈ T, (P.memAt mT (yf i') : ℝ)) =
        (P.memWeight (Function.update mT y (mT y + 1)) * ((mT y : ℝ) + 1)) *
          ∏ i' ∈ T, (P.memAt mT (yf i') : ℝ) := by ring
      _ = P.lam y * (P.memWeight mT * ∏ i' ∈ T, (P.memAt mT (yf i') : ℝ)) := by
          rw [hw]; ring
      _ = _ := by rw [ih hyT, hlam]; ring

lemma promCount_eq_cntF (z' : ℤ × ℤ) (tg : Fin P.K → ℕ × Bool) (c : EC P) (hc : c.2.2 = tg)
    (y : P.PT) : P.promCount z' tg y = cntF P (promSet P c) (P.promPart z' tg) y := by
  unfold MemParams.promCount cntF promSet
  rw [filter_filter, hc]

/-- **The reversal weight identity**: `μ(s) rfac(s,c) ∏_I Vᵢ = μ(s') rfac(s',c') ∏_{St} Vᵢ`. -/
lemma weight_rev (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) (h : ECond P ω s c)
    (hV : ∀ i, P.Vg i ≠ 0) :
    P.stWeight s * rfac P s c * ∏ i ∈ promSet P c, P.Vg i =
      P.stWeight (P.edgeOut s c) * rfac P (P.edgeOut s c) (revC P s c) *
        ∏ i ∈ c.1, P.Vg i := by
  obtain ⟨_, hpp, hsp, hpc⟩ := h
  rcases s with ⟨z, ℓ, m⟩
  rcases c with ⟨St, z', tg⟩
  have hI : promSet P (St, z', tg) = univ.filter fun i => (tg i).2 = true := rfl
  set I := univ.filter fun i => (tg i).2 = true with hIdef
  set Pc := cntF P I (P.promPart z' tg)
  set Sc := cntF P St (P.storedPart z ℓ)
  set m₀ := m - Pc
  have hPc : ∀ y, P.promCount z' tg y = Pc y := fun y =>
    promCount_eq_cntF P z' tg (St, z', tg) rfl y
  have hpc' : ∀ y, Pc y ≤ m y := fun y => (hPc y) ▸ hpc y
  have hm : m = m₀ + Pc := by
    funext y; simp only [m₀, Pi.add_apply, Pi.sub_apply]
    have := hpc' y; omega
  have hm' : P.edgeOutMem (z, ℓ, m) (St, z', tg) = m₀ + Sc := by
    funext y
    show m y - P.promCount z' tg y + P.storeCount z ℓ St y = (m - Pc) y + Sc y
    rw [hPc]; rfl
  have hout : P.edgeOut (z, ℓ, m) (St, z', tg) =
      (z', P.newList ℓ (fun i => (tg i).1), m₀ + Sc) := by
    simp only [MemParams.edgeOut]; rw [hm']
  have hmem_rev : P.edgeOutMem (P.edgeOut (z, ℓ, m) (St, z', tg)) (revC P (z, ℓ, m) (St, z', tg))
      = m := edgeOutMem_rev P (z, ℓ, m) (St, z', tg) hpc
  have hF1 := fock_prod P I (P.promPart z' tg) (fun i => rfl)
    (fun i hi => hpp i (by simpa [I] using hi)) m₀
  have hF2 := fock_prod P St (P.storedPart z ℓ) (fun i => rfl) (fun i hi => hsp i hi) m₀
  rw [← hm] at hF1
  set A := ∏ i ∈ I, (P.memAt m (P.promPart z' tg i) : ℝ)
  set Bn := ∏ i ∈ univ.filter (fun i => ¬ (tg i).2 = true), P.nu i (tg i).1
  set A' := ∏ i ∈ St, (P.memAt (m₀ + Sc) (P.storedPart z ℓ i) : ℝ)
  set Bl := ∏ i ∈ univ.filter (fun i => ¬ i ∈ St), P.nu i (ℓ i (Fin.last P.J))
  have hVI : ∏ i ∈ I, P.Vg i ≠ 0 := prod_ne_zero_iff.2 fun i _ => hV i
  have hVS : ∏ i ∈ St, P.Vg i ≠ 0 := prod_ne_zero_iff.2 fun i _ => hV i
  have c1 : rfac P (z, ℓ, m) (St, z', tg) * ∏ i ∈ I, P.Vg i =
      memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * (A * Bn) := by
    unfold rfac
    rw [hm']
    simp only []
    rw [prod_ite, prod_div_distrib]
    simp only [A, Bn, I]
    have hVI' : (∏ x ∈ univ.filter (fun x => (tg x).2 = true), P.Vg x) ≠ 0 := hVI
    field_simp
  have c2 : rfac P (P.edgeOut (z, ℓ, m) (St, z', tg)) (revC P (z, ℓ, m) (St, z', tg)) *
      ∏ i ∈ St, P.Vg i =
      memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * (A' * Bl) := by
    unfold rfac
    rw [hmem_rev, hout]
    simp only [revC, decide_eq_true_eq]
    rw [prod_ite, prod_div_distrib]
    have hfil : univ.filter (fun i => i ∈ St) = St := by ext i; simp
    rw [hfil]
    simp only [A', Bl]
    have e : ∀ x, P.promPart z (fun i => (ℓ i (Fin.last P.J), decide (i ∈ St))) x =
        P.storedPart z ℓ x := fun x => rfl
    simp only [e]
    field_simp
  have c5a : (∏ i ∈ I, P.nu i (P.promPart z' tg i).2.1) * Bn = ∏ i, P.nu i (tg i).1 :=
    prod_filter_mul_prod_filter_not univ (fun i => (tg i).2 = true) _
  have c5b : (∏ i ∈ St, P.nu i (P.storedPart z ℓ i).2.1) * Bl =
      ∏ i, P.nu i (ℓ i (Fin.last P.J)) := by
    rw [← prod_filter_mul_prod_filter_not univ (fun i => i ∈ St)]
    have hfil : univ.filter (fun i => i ∈ St) = St := by ext i; simp
    rw [hfil]; rfl
  have hLW := listWeight_newList_mul P ℓ (fun i => (tg i).1)
  rw [hI]
  unfold MemParams.stWeight
  rw [hout] at c2
  rw [hout, mul_assoc, c1, mul_assoc (P.listWeight _ * P.memWeight _)]
  simp only []
  rw [c2]
  calc P.listWeight ℓ * P.memWeight m *
        (memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * (A * Bn)) =
      memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * P.listWeight ℓ *
        ((P.memWeight m * A) * Bn) := by ring
    _ = memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * P.memWeight m₀ *
        (P.listWeight ℓ * ∏ i, P.nu i (tg i).1) := by rw [hF1, ← c5a]; ring
    _ = memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * P.memWeight m₀ *
        (P.listWeight (P.newList ℓ fun i => (tg i).1) * ∏ i, P.nu i (ℓ i (Fin.last P.J))) := by
        rw [hLW]
    _ = memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) *
        P.listWeight (P.newList ℓ fun i => (tg i).1) * ((P.memWeight (m₀ + Sc) * A') * Bl) := by
        rw [hF2, ← c5b]; ring
    _ = _ := by ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: column sums of edge pieces are row sums of the reversed pieces

`coeffP Qc κ` is the edge coefficient restricted to the classes `Qc St I` (stored groups `St`,
promoted groups `I`) with the geometric multiplier replaced by `κ`. `col_via_rev`: the weighted
column sum of `coeffP Qc κ` against `Φ ≥ 0` is at most `3^K` times the row sum of
`coeffP Qc' κ'` against `Φ`, when `Qc St I → Qc' I St` and `‖κ t a b D‖ ≤ ‖κ' (−t) b a D‖`
(`1/2 ≤ Vᵢ ≤ 3/2`, nonnegative `ν`). -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

open Classical in
/-- The edge coefficient restricted to a class of (stores, promotions), multiplier `κ`. -/
noncomputable def coeffP (Qc : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) : ℂ :=
  if Qc c.1 (promSet P c) then coeffK P κ ω s c else 0

lemma lam_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (y : P.PT) : 0 ≤ P.lam y := by
  have h := y.2
  simp only [MemParams.partSet, mem_biUnion, mem_univ, true_and, mem_image, mem_range] at h
  obtain ⟨i, p, hp, l, _, he⟩ := h
  unfold MemParams.lam; rw [← he]; exact hnu i p hp

lemma stWeight_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (s : P.MState) (hs : s ∈ P.stSet) :
    0 ≤ P.stWeight s := by
  simp only [MemParams.stSet, mem_product] at hs
  unfold MemParams.stWeight MemParams.memWeight MemParams.listWeight
  refine mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun k _ => ?_)
    (prod_nonneg fun y _ => by have := lam_nonneg P hnu y; positivity)
  apply hnu
  have := hs.2.1
  simp only [listCands, Fintype.mem_piFinset] at this
  exact this i k

lemma memRho_nonneg : (0 : ℝ) ≤ memRho := by unfold memRho; norm_num

lemma rfac_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV : ∀ i, 0 ≤ P.Vg i)
    (s : P.MState) (c : EC P) (hc : c ∈ P.edgeChoices) : 0 ≤ rfac P s c := by
  unfold rfac
  have hρ := memRho_nonneg
  refine mul_nonneg (mul_nonneg (pow_nonneg hρ _) (prod_nonneg fun i _ => ?_)) (pow_nonneg hρ _)
  split_ifs
  · exact div_nonneg (Nat.cast_nonneg _) (hV i)
  · apply hnu
    simp only [MemParams.edgeChoices, mem_product, mem_univ, true_and,
      Fintype.mem_piFinset] at hc
    exact (hc.2 i).1

lemma revC_mem (s : P.MState) (hs : s ∈ P.stSet) (c : EC P) :
    revC P s c ∈ P.edgeChoices := by
  simp only [MemParams.stSet, mem_product] at hs
  simp only [MemParams.edgeChoices, mem_product, mem_univ, true_and, Fintype.mem_piFinset, revC]
  refine ⟨hs.1, fun i => ⟨?_, trivial⟩⟩
  have := hs.2.1
  simp only [listCands, Fintype.mem_piFinset] at this
  exact this i _

lemma promSet_revC (s : P.MState) (c : EC P) : promSet P (revC P s c) = c.1 := by
  ext i; simp [promSet, revC]

/-- `∏_{St} Vᵢ / ∏_I Vᵢ ≤ 3^K` when `1/2 ≤ Vᵢ ≤ 3/2`. -/
lemma prod_ratio_le (St I : Finset (Fin P.K)) (hV1 : ∀ i, 1 / 2 ≤ P.Vg i)
    (hV2 : ∀ i, P.Vg i ≤ 3 / 2) :
    (∏ i ∈ St, P.Vg i) ≤ 3 ^ P.K * ∏ i ∈ I, P.Vg i := by
  have h1 : ∏ i ∈ St, P.Vg i ≤ (3 / 2) ^ P.K := by
    calc ∏ i ∈ St, P.Vg i ≤ ∏ i ∈ St, (3 / 2 : ℝ) :=
          prod_le_prod (fun i _ => by linarith [hV1 i]) fun i _ => hV2 i
      _ = (3 / 2) ^ St.card := by rw [prod_const]
      _ ≤ (3 / 2) ^ P.K := by
          apply pow_le_pow_right₀ (by norm_num)
          exact (card_le_univ St).trans (by simp)
  have h2 : (1 / 2 : ℝ) ^ P.K ≤ ∏ i ∈ I, P.Vg i := by
    calc (1 / 2 : ℝ) ^ P.K ≤ (1 / 2) ^ I.card := by
          apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
          exact (card_le_univ I).trans (by simp)
      _ = ∏ i ∈ I, (1 / 2 : ℝ) := by rw [prod_const]
      _ ≤ ∏ i ∈ I, P.Vg i := prod_le_prod (fun _ _ => by norm_num) fun i _ => hV1 i
  calc ∏ i ∈ St, P.Vg i ≤ (3 / 2) ^ P.K := h1
    _ = 3 ^ P.K * (1 / 2) ^ P.K := by rw [← mul_pow]; norm_num
    _ ≤ 3 ^ P.K * ∏ i ∈ I, P.Vg i := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Columns via reversal.** -/
theorem col_via_rev (Qc Qc' : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (hQc : ∀ St I, Qc St I → Qc' I St) (κ κ' : ℤ → ℕ → ℕ → ℕ → ℂ)
    (hκ : ∀ t a b D, ‖κ t a b D‖ ≤ ‖κ' (-t) b a D‖) (ω : ℝ × ℝ × ℝ)
    (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV1 : ∀ i, 1 / 2 ≤ P.Vg i)
    (hV2 : ∀ i, P.Vg i ≤ 3 / 2) (Φ : P.MState → ℝ) (hΦ : ∀ s, 0 ≤ Φ s) :
    ∑ s ∈ P.stSet, ∑ c ∈ P.edgeChoices, P.stWeight s * ‖coeffP P Qc κ ω s c‖ *
      (if P.edgeOut s c ∈ P.stSet then Φ (P.edgeOut s c) else 0) ≤
    3 ^ P.K * ∑ s' ∈ P.stSet, Φ s' * ∑ c' ∈ P.edgeChoices,
      P.stWeight s' * ‖coeffP P Qc' κ' ω s' c'‖ := by
  classical
  have hVnn : ∀ i, 0 ≤ P.Vg i := fun i => by linarith [hV1 i]
  have hV0 : ∀ i, P.Vg i ≠ 0 := fun i => by linarith [hV1 i]
  set S := P.stSet ×ˢ P.edgeChoices
  set A := S.filter fun q => ECond P ω q.1 q.2 ∧ Qc q.2.1 (promSet P q.2) ∧
    P.edgeOut q.1 q.2 ∈ P.stSet
  set F : P.MState × EC P → ℝ := fun q => P.stWeight q.1 * ‖coeffP P Qc' κ' ω q.1 q.2‖ * Φ q.1
  set rv : P.MState × EC P → P.MState × EC P := fun q => (P.edgeOut q.1 q.2, revC P q.1 q.2)
  -- the left side as a sum over `A`
  have hL : ∑ s ∈ P.stSet, ∑ c ∈ P.edgeChoices, P.stWeight s * ‖coeffP P Qc κ ω s c‖ *
      (if P.edgeOut s c ∈ P.stSet then Φ (P.edgeOut s c) else 0) =
      ∑ q ∈ A, P.stWeight q.1 * ‖coeffP P Qc κ ω q.1 q.2‖ * Φ (P.edgeOut q.1 q.2) := by
    rw [← sum_product (s := P.stSet) (t := P.edgeChoices)
      (f := fun q => P.stWeight q.1 * ‖coeffP P Qc κ ω q.1 q.2‖ *
        (if P.edgeOut q.1 q.2 ∈ P.stSet then Φ (P.edgeOut q.1 q.2) else 0)), sum_filter]
    refine sum_congr rfl fun q _ => ?_
    by_cases h1 : ECond P ω q.1 q.2 ∧ Qc q.2.1 (promSet P q.2) ∧ P.edgeOut q.1 q.2 ∈ P.stSet
    · rw [if_pos h1, if_pos h1.2.2]
    · rw [if_neg h1]
      by_cases h2 : P.edgeOut q.1 q.2 ∈ P.stSet
      · have : coeffP P Qc κ ω q.1 q.2 = 0 := by
          unfold coeffP coeffK
          by_cases h3 : Qc q.2.1 (promSet P q.2)
          · rw [if_pos h3, if_neg (fun h4 => h1 ⟨h4, h3, h2⟩)]
          · rw [if_neg h3]
        rw [this]; simp
      · rw [if_neg h2]; simp
  -- each term is dominated by `3^K F (rv q)`
  have hterm : ∀ q ∈ A, P.stWeight q.1 * ‖coeffP P Qc κ ω q.1 q.2‖ * Φ (P.edgeOut q.1 q.2) ≤
      3 ^ P.K * F (rv q) := by
    intro q hq
    simp only [A, mem_filter, S, mem_product] at hq
    obtain ⟨⟨hs, hc⟩, hE, hQq, hout⟩ := hq
    have hE' := econd_rev P ω q.1 q.2 hE
    have hD : (padProd q.1.2.1 : ℤ) ∣ detZ q.1.1 q.2.2.1 := hE.1.2.2.2.2.1
    have hw := weight_rev P ω q.1 q.2 hE hV0
    have hrf := rfac_nonneg P hnu hVnn q.1 q.2 hc
    have hrf' := rfac_nonneg P hnu hVnn (P.edgeOut q.1 q.2) _ (revC_mem P q.1 hs q.2)
    have hμ := stWeight_nonneg P hnu q.1 hs
    have hμ' := stWeight_nonneg P hnu _ hout
    have hc1 : ‖coeffP P Qc κ ω q.1 q.2‖ = rfac P q.1 q.2 * ‖κ (detZ q.1.1 q.2.2.1 /
        padProd q.1.2.1) (∏ i, (q.2.2.2 i).1) (lastProd q.1.2.1) (padProd q.1.2.1)‖ := by
      unfold coeffP coeffK
      rw [if_pos hQq, if_pos hE, norm_mul, Complex.norm_real, Real.norm_of_nonneg hrf]
    have hc2 : ‖coeffP P Qc' κ' ω (rv q).1 (rv q).2‖ = rfac P (rv q).1 (rv q).2 *
        ‖κ' (-(detZ q.1.1 q.2.2.1 / padProd q.1.2.1)) (lastProd q.1.2.1)
          (∏ i, (q.2.2.2 i).1) (padProd q.1.2.1)‖ := by
      unfold coeffP coeffK
      simp only [rv]
      have hr1 : (revC P q.1 q.2).1 = promSet P q.2 := rfl
      rw [promSet_revC, hr1, if_pos (hQc _ _ hQq), if_pos hE', norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hrf', det_rev P q.1 q.2 hD, prod_labels_rev, lastProd_out,
        padProd_out]
    have hratio := prod_ratio_le P q.2.1 (promSet P q.2) hV1 hV2
    have hpos : 0 < ∏ i ∈ promSet P q.2, P.Vg i := prod_pos fun i _ => by linarith [hV1 i]
    -- μ rfac ≤ 3^K μ' rfac'
    have hμr : P.stWeight q.1 * rfac P q.1 q.2 ≤
        3 ^ P.K * (P.stWeight (rv q).1 * rfac P (rv q).1 (rv q).2) := by
      have h1 : P.stWeight q.1 * rfac P q.1 q.2 * ∏ i ∈ promSet P q.2, P.Vg i ≤
          3 ^ P.K * (P.stWeight (rv q).1 * rfac P (rv q).1 (rv q).2) *
            ∏ i ∈ promSet P q.2, P.Vg i := by
        rw [hw]
        calc P.stWeight (P.edgeOut q.1 q.2) * rfac P (P.edgeOut q.1 q.2) (revC P q.1 q.2) *
              ∏ i ∈ q.2.1, P.Vg i ≤
            P.stWeight (P.edgeOut q.1 q.2) * rfac P (P.edgeOut q.1 q.2) (revC P q.1 q.2) *
              (3 ^ P.K * ∏ i ∈ promSet P q.2, P.Vg i) :=
              mul_le_mul_of_nonneg_left hratio (mul_nonneg hμ' hrf')
          _ = _ := by simp only [rv]; ring
      exact le_of_mul_le_mul_right h1 hpos
    have hκq := hκ (detZ q.1.1 q.2.2.1 / padProd q.1.2.1) (∏ i, (q.2.2.2 i).1)
      (lastProd q.1.2.1) (padProd q.1.2.1)
    have hΦq := hΦ (P.edgeOut q.1 q.2)
    simp only [F]
    rw [hc1, hc2]
    calc P.stWeight q.1 * (rfac P q.1 q.2 * ‖κ (detZ q.1.1 q.2.2.1 / ↑(padProd q.1.2.1))
          (∏ i, (q.2.2.2 i).1) (lastProd q.1.2.1) (padProd q.1.2.1)‖) *
          Φ (P.edgeOut q.1 q.2) =
        (P.stWeight q.1 * rfac P q.1 q.2) * ‖κ (detZ q.1.1 q.2.2.1 / ↑(padProd q.1.2.1))
          (∏ i, (q.2.2.2 i).1) (lastProd q.1.2.1) (padProd q.1.2.1)‖ *
          Φ (P.edgeOut q.1 q.2) := by ring
      _ ≤ (3 ^ P.K * (P.stWeight (rv q).1 * rfac P (rv q).1 (rv q).2)) *
          ‖κ' (-(detZ q.1.1 q.2.2.1 / ↑(padProd q.1.2.1))) (lastProd q.1.2.1)
            (∏ i, (q.2.2.2 i).1) (padProd q.1.2.1)‖ * Φ (P.edgeOut q.1 q.2) := by
          gcongr
      _ = _ := by simp only [rv]; ring
  -- `rv` is injective on `A` and maps into `S`
  have hinj : Set.InjOn rv A := by
    intro q hq q' hq' heq
    simp only [A, coe_filter, Set.mem_ofPred_eq] at hq hq'
    have e1 : rv (rv q) = q := by
      simp only [rv]
      rw [edgeOut_rev P q.1 q.2 hq.2.1.2.2.2, revC_rev P q.1 q.2 hq.2.1.2.2.2]
    have e2 : rv (rv q') = q' := by
      simp only [rv]
      rw [edgeOut_rev P q'.1 q'.2 hq'.2.1.2.2.2, revC_rev P q'.1 q'.2 hq'.2.1.2.2.2]
    rw [← e1, ← e2, heq]
  have hmaps : ∀ q ∈ A, rv q ∈ S := by
    intro q hq
    simp only [A, mem_filter, S, mem_product] at hq
    simp only [S, mem_product, rv]
    exact ⟨hq.2.2.2, revC_mem P q.1 hq.1.1 q.2⟩
  have hFnn : ∀ q ∈ S, 0 ≤ F q := by
    intro q hq
    simp only [S, mem_product] at hq
    exact mul_nonneg (mul_nonneg (stWeight_nonneg P hnu q.1 hq.1) (norm_nonneg _)) (hΦ _)
  rw [hL]
  calc ∑ q ∈ A, P.stWeight q.1 * ‖coeffP P Qc κ ω q.1 q.2‖ * Φ (P.edgeOut q.1 q.2) ≤
      ∑ q ∈ A, 3 ^ P.K * F (rv q) := sum_le_sum hterm
    _ = 3 ^ P.K * ∑ q ∈ A.image rv, F q := by rw [mul_sum, sum_image hinj]
    _ ≤ 3 ^ P.K * ∑ q ∈ S, F q := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨q₀, hq₀, rfl⟩ := mem_image.1 hq
          exact hmaps q₀ hq₀
        · intro q hq _; exact hFnn q hq
    _ = _ := by
        congr 1
        rw [sum_product]
        refine sum_congr rfl fun s' _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun c' _ => ?_
        simp only [F]; ring

end ArtinPrimitiveRoots.L102G
end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinBV

open Finset

end ArtinBV
end

section
/-! # L102D: the exact outer reduction of (10.9) ([21] §3.1, (3.10)–(3.11))

`Q_Y − Q_Y^maj = Q^sh − Q^{maj,sh} + Q^min`, where `Q^sh`, `Q^{maj,sh}` are the parts of the two
squares over label pairs whose products `a, b` are not coprime, and `Q^min` is the coprime part
of the minor-arc square, with kernel `ψ(t/Y) ∫_{[0,1) ∖ 𝔐} e(θ(t − b + a)) dθ`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary inputs -/

/-- `∫_{[0,1)} e(θ n) dθ = 1_{n = 0}`. -/
lemma integral_Ico_exp_int (n : ℤ) :
    ∫ θ in Set.Ico (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * ((θ * n : ℝ) : ℂ)) =
      if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn; simp
  · rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, this, Complex.I_ne_zero]
    have := integral_exp_mul_complex (a := 0) (b := 1) hc
    simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [show (fun θ : ℝ => Complex.exp (2 * π * Complex.I * ((θ : ℂ) * n))) =
        fun θ : ℝ => Complex.exp (2 * π * Complex.I * n * θ) by
      funext θ; ring_nf]
    rw [this]
    have h1 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one,
        show (2 * π * Complex.I * n : ℂ) = n * (2 * π * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1]; simp

lemma majorArcs_subset (x A₀ Y : ℝ) : majorArcs x A₀ Y ⊆ Set.Ico 0 1 :=
  fun _ h => ⟨h.1, h.2.1⟩

lemma measurableSet_majorArcs (x A₀ Y : ℝ) : MeasurableSet (majorArcs x A₀ Y) := by
  have : majorArcs x A₀ Y = Set.Ico 0 1 ∩ ⋃ k : ℕ, ⋃ c : ℤ,
      {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} := by
    ext θ
    simp only [majorArcs, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ico, Set.mem_iUnion]
    constructor
    · rintro ⟨h0, h1, k, hk1, hk2, c, hc, hd⟩; exact ⟨⟨h0, h1⟩, k, c, hk1, hk2, hc, hd⟩
    · rintro ⟨⟨h0, h1⟩, k, c, hk1, hk2, hc, hd⟩; exact ⟨h0, h1, k, hk1, hk2, c, hc, hd⟩
  rw [this]
  refine measurableSet_Ico.inter (MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun c => ?_)
  by_cases hP : 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1
  · have : {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} = {θ : ℝ | |θ - c / k| ≤ 2 * log x ^ A₀ / Y} := by
      ext θ; simp only [Set.mem_ofPred_eq]; tauto
    rw [this]
    exact measurableSet_le (by fun_prop) measurable_const
  · have : {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} = ∅ := by
      ext θ; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; tauto
    rw [this]; exact MeasurableSet.empty

/-- `H_𝔪 = ψ(t/Y) 1_{t = b − a} − H_𝔐`. -/
lemma minorKernel_eq (x A₀ Y : ℝ) (t a b : ℤ) :
    minorKernel x A₀ Y t a b =
      (arcCutoff (t / Y) : ℂ) * (if t - b + a = 0 then 1 else 0) - majorKernel x A₀ Y t a b := by
  unfold minorKernel majorKernel
  have hint : IntegrableOn (fun θ : ℝ =>
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))) (Set.Ico 0 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ico_subset_Icc_self
  rw [setIntegral_sdiff (measurableSet_majorArcs x A₀ Y) hint (majorArcs_subset x A₀ Y), mul_sub]
  congr 2
  have := integral_Ico_exp_int (t - b + a)
  push_cast at this ⊢
  rw [this]

/-! ## The identity -/

/-! ## The reduction of (10.9) to the shared-label bound (D1b) and the minor-arc bound (D1c) -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: good positions and their measure ([21] §3.2, Lemma 3.2)

For lists `ℓ` of `M` primes in each group, the omission products `D` (omit one label per group),
the two good-state tests on a ratio `r ∈ ℝ/ℤ` (realized on `(0, 1]`), and Lemma 3.2: the set of
`r` failing goodness has measure at most `exp(-c L^{0.1})`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Distance to the nearest integer and its level sets -/

/-! ## Test (i): the union bound -/

/-! ## Markov's inequality for a finite weighted family of bad sets -/

/-! ## Test (ii): one fresh draw, then Markov over the fresh draws -/

/-! ## Counting and asymptotics -/

/-! ## Lemma 3.2 -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the divisor input (3.9) of [21] §3.1

`∑_{h ≤ Z} τ(1 + l h)² ≤ 4 (Z + T)(1 + log T)³` whenever every `m` with `m⁴ ≤ (1 + lZ)³` is
`≤ T`. The proof replaces `τ(n)² = #{(d₁, d₂) : d₁, d₂ ∣ n}` by four times the number of divisor
pairs with `lcm⁴ ≤ n³` (one of `(d₁,d₂)`, `(n/d₁,n/d₂)`, `(d₁,n/d₂)`, `(n/d₁,d₂)` qualifies), and
then counts `h` in one residue class modulo the `lcm`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the shared-label parts are negligible ([21] §3.1 (3.9), §4.9 (4.61), (4.63))

Bounds for the inner sums `rawInner`, `majInner` at one pair of label products, for the measure of
the major arcs, and for the normalized mass of label pairs with a common prime. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary facts about the cutoffs and coefficients -/

lemma dyadicBump_nonneg (u : ℝ) : 0 ≤ dyadicBump u := by
  unfold dyadicBump
  rcases le_or_gt u 0 with hu | hu
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]; simp
  · exact sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

lemma dyadicBump_le_one (u : ℝ) : dyadicBump u ≤ 1 := by
  unfold dyadicBump
  linarith [Real.smoothTransition.le_one (u - 1), Real.smoothTransition.nonneg (u / 2 - 1)]

lemma abs_arcCutoff_le (u : ℝ) : |arcCutoff u| ≤ if |u| < 5 then 1 else 0 := by
  unfold arcCutoff
  have h1 := Real.smoothTransition.nonneg (5 - u)
  have h2 := Real.smoothTransition.nonneg (5 + u)
  have h3 := Real.smoothTransition.le_one (5 - u)
  have h4 := Real.smoothTransition.le_one (5 + u)
  rw [abs_of_nonneg (mul_nonneg h1 h2)]
  split_ifs with hu
  · nlinarith
  · rw [abs_lt] at hu
    push Not at hu
    by_cases hu' : u ≤ -5
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 + u ≤ 0), mul_zero]
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith [hu (not_le.1 hu')] : 5 - u ≤ 0),
        zero_mul]

/-! ## The measure of the major arcs -/

/-! ## The raw inner sum at one pair of label products -/

/-! ## The major inner sum at one pair of label products -/

lemma norm_majorKernel_le (x A₀ Y : ℝ) (t a b : ℤ) :
    ‖majorKernel x A₀ Y t a b‖ ≤
      (if |(t : ℝ) / Y| < 5 then 1 else 0) * (volume (majorArcs x A₀ Y)).toReal := by
  unfold majorKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hfin : volume (majorArcs x A₀ Y) < ⊤ :=
    (measure_mono (majorArcs_subset x A₀ Y)).trans_lt (by simp)
  have hint : ‖∫ θ in majorArcs x A₀ Y,
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))‖ ≤
      1 * volume.real (majorArcs x A₀ Y) := by
    refine norm_setIntegral_le_of_norm_le_const hfin fun θ _ => ?_
    rw [Complex.norm_exp]
    simp
  rw [one_mul] at hint
  exact mul_le_mul (abs_arcCutoff_le _) hint (norm_nonneg _) (by split_ifs <;> norm_num)

/-! ## The mass of label pairs with a common prime -/

/-! ## Inputs about the groups for large `x` -/

/-! ## Numerics -/


/-! ## D1b: the shared-label bound -/

/-- Common setting: the hypotheses used by both halves of D1b, at one `x`. -/
structure SharedSetting (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (C : ℝ) :
    Prop where
  hL1 : 1 ≤ log x
  hx : 0 < x
  hHm : 0 < Hm
  hHn : 0 < Hn
  hY : 1 ≤ Y
  hX1 : 1 ≤ Hm * Hn
  hα0 : α 0 = 0
  hβ0 : β 0 = 0
  hαb : ∀ m, ‖α m‖ ≤ log x ^ C
  hβb : ∀ n, ‖β n‖ ≤ log x ^ C
  hV : ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j)
  hab : ∀ i, (0.1 : ℝ) < a i
  hlog : 1 + log (17 * (Hm * Hn)) ≤ 2 * log x


end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: root coordinates of a primitive position (for D7p)

For a primitive `P₀ = (u, v)` with `u ≥ 1`: `c = (−v⁻¹ mod u)`, `d = (1 + vc)/u`, the completion
`g = (u c; v d) ∈ SL₂(ℤ)`, `g z = (u z₁ + c z₂, v z₁ + d z₂)` and its inverse. Box conditions,
divisibility, goodness and the damping count transfer between `P = g z` and `z`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-! ## Goodness is invariant under integer shifts of the ratio -/

/-! ## The ratio of `g z` -/

lemma detZ_complVec {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) : detZ z (complVec z) = 1 := by
  unfold detZ complVec; dsimp only
  have := Int.gcd_eq_gcd_ab z.1 z.2
  rw [hz] at this; push_cast at this
  linarith

/-! ## The damping count -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the cuts of D1c (`minor_square_bound`) and the reduction

Four statements about the operator model of `L102D_OpDefs` (draft bundle
`Def_ArtinMinorOperator`):

* `MomentBoundStmt` (D7, [21] (3.19)/(4.1)): the moment of `(AA*)^R` is `≤ UV L^{-E₀ N}`;
* `PairingFromMomentStmt` (D5, [21] (3.20)): the pairing `⟨f, A f⟩_σ` is controlled by the moment;
* `GoodnessRemovalStmt` (D8a, [21] (4.56)–(4.57)): removing `G` from the pairing costs `UV L^{-A}`;
* `PadLiftStmt` (D8bc, [21] (4.58)–(4.63)): `Q^min = ∑_{dyads} d₀⁻¹ ⟨f, S T S f⟩_σ + O(XY L^{-A})`.

`minor_square_bound_of_cuts` proves the D1c statement from the four. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the cuts of D7 (the moment (4.1)) and the reduction

Seven statements about the draft model `L102D_OpDefs` + `L102D_MemDefs`, in the order of the
proof of [21] Proposition 4.1:

* `PathExpansionStmt` (D7p, exact): the physical moment is the sum over primitive roots `P₀` of
  the path functional in root coordinates, [21] §3.5 (3.30)–(3.32).
* `RootReplacementStmt` (D7r, [21] Lemma 3.4): the sum over roots is `UV/ζ(2)` times the integral
  of the independent-line moment over `[1,16] × [1,2] × [0,1]`, up to `UV L^{-AN}`.
* `MemoryIdentityStmt` (D7a, exact, [21] (4.5)–(4.15)): the independent-line moment is the
  baseline times the memory moment with global birth distinctness (no truncation).
* `TruncationStmt` (D7b, [21] (4.16)): truncating the memory at `B = ⌈L²⌉` costs `L^{-AN}`.
* `GhostBoundStmt` (D7c, [21] (4.19)–(4.22)): `‖G_j‖ ≤ C_K` on `H_B`.
* `EdgeBoundStmt` (D7d, [21] (4.23)–(4.42)): `‖E_j‖ ≤ L^{-G}` on `H_B`, `A₀` and then `K` large.
* `DistinctnessStmt` (D7e, [21] (4.43)–(4.55)): given D7c and D7d, the truncated memory moment
  with global birth distinctness is `≤ L^{-(G-1)N}`.

`moment_bound_of_cuts` proves `MomentBoundStmt` (D7) from them. -/

-- `MemParams.RootIn` now lives in the bundle `Def_ArtinMemoryModel` (round 5).

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: membership in the memory model's finite sets, in closed form

`(Finset.mem_product.1 h).2` on `h : x ∈ P.edgeChoices` (or `P.stSet`, `P.ghostChoices`) makes the
elaborator unify through the membership instances down to `Multiset.bind` of `zSet` (≈ 1 s per use,
measured). These closed-form iff lemmas avoid it. -/

namespace ArtinPrimitiveRoots.L102D

open Finset

variable (P : MemParams)

lemma mem_edgeChoices_iff' (c : Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)) :
    c ∈ P.edgeChoices ↔ c.1 ∈ (univ : Finset (Finset (Fin P.K))) ∧ c.2.1 ∈ P.zSet ∧
      c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ (univ : Finset Bool) := by
  rw [MemParams.edgeChoices, mem_product, mem_product]

lemma tg_mem_of_mem_edgeChoices {c : Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)}
    (hc : c ∈ P.edgeChoices) :
    c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ (univ : Finset Bool) :=
  ((mem_edgeChoices_iff' P c).1 hc).2.2

lemma mem_stSet_iff' (s : P.MState) :
    s ∈ P.stSet ↔ s.1 ∈ P.zSet ∧ s.2.1 ∈ listCands P.x P.a P.J ∧ s.2.2 ∈ P.memSet := by
  rw [MemParams.stSet, mem_product, mem_product]

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: crude edge rows ([21] (4.23)–(4.25)) with forced fresh labels (for D7e)

* `target_count`: at most `16` targets `z'` in the box with `det(z, z') = j₁` (`z' = h z + j₁ w`,
  `τ(z')/τ(z) ∈ [1/16, 16]`);
* `norm_edgeMult_le`: `‖edgeMult‖ ≤ 1[|t| < 5Y] (1[t = b − a] + vol 𝔐)`;
* `edge_row`: the weighted absolute row sum of an edge with any multiplier `κ` of that shape, with
  the fresh labels of the groups in `C` forced into a set `V`. Uses prover G's `coeffK`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

section Geo

variable (P : MemParams)

lemma tauR_decomp (ω : ℝ × ℝ × ℝ) {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) (z' : ℤ × ℤ) :
    tauR ω z' = (detZ z' (complVec z) : ℝ) * tauR ω z + (detZ z z' : ℝ) * tauR ω (complVec z) := by
  have hdet := detZ_complVec hz
  unfold detZ at hdet ⊢
  unfold tauR
  have h1 : (z'.1 : ℝ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1 : ℤ) * z.1 +
      (z.1 * z'.2 - z.2 * z'.1 : ℤ) * (complVec z).1 := by
    have : (z'.1 : ℤ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1) * z.1 +
        (z.1 * z'.2 - z.2 * z'.1) * (complVec z).1 := by linear_combination (-z'.1) * hdet
    exact_mod_cast this
  have h2 : (z'.2 : ℝ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1 : ℤ) * z.2 +
      (z.1 * z'.2 - z.2 * z'.1 : ℤ) * (complVec z).2 := by
    have : (z'.2 : ℤ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1) * z.2 +
        (z.1 * z'.2 - z.2 * z'.1) * (complVec z).2 := by linear_combination (-z'.2) * hdet
    exact_mod_cast this
  rw [h1, h2]; push_cast; ring

lemma eq_of_det_eq {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) {z' z'' : ℤ × ℤ}
    (h1 : detZ z z' = detZ z z'') (h2 : detZ z' (complVec z) = detZ z'' (complVec z)) : z' = z'' := by
  have hdet := detZ_complVec hz
  unfold detZ at hdet h1 h2
  ext
  · linear_combination (z''.1 - z'.1) * hdet + (complVec z).1 * h1 + z.1 * h2
  · linear_combination (z''.2 - z'.2) * hdet + (complVec z).2 * h1 + z.2 * h2

open Classical in
/-- **At most 16 targets per determinant.** -/
lemma target_count (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) {z : ℤ × ℤ}
    (hz : Int.gcd z.1 z.2 = 1) (hbox : P.InBox ω z) (j₁ : ℤ) :
    (P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = j₁)).card ≤ 16 := by
  obtain ⟨hu1, hu2, -, -, -, -⟩ := hω
  have hu : 0 < ω.1 := by linarith
  have htz : P.U / ω.1 ≤ tauR ω z := by
    rw [div_le_iff₀ hu, mul_comm]; exact hbox.1
  have htz0 : 0 < tauR ω z := lt_of_lt_of_le (by positivity) htz
  set w := complVec z
  set lo : ℝ := (P.U / ω.1 - j₁ * tauR ω w) / tauR ω z
  -- the coordinate `h = det(z', w)` lies in a window of length 15
  have hwin : ∀ z' ∈ P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = j₁),
      detZ z' w ∈ Icc ⌈lo⌉ (⌈lo⌉ + 15) := by
    intro z' hz'
    obtain ⟨-, hb', hd'⟩ := mem_filter.1 hz'
    have hdec := tauR_decomp ω hz z'
    rw [hd'] at hdec
    have hlow : P.U / ω.1 ≤ tauR ω z' := by
      rw [div_le_iff₀ hu, mul_comm]; exact hb'.1
    have hhigh : tauR ω z' ≤ 16 * P.U / ω.1 := by
      rw [le_div_iff₀ hu, mul_comm]; exact hb'.2.1
    have hh : (detZ z' w : ℝ) = (tauR ω z' - j₁ * tauR ω w) / tauR ω z := by
      rw [eq_div_iff htz0.ne']; linarith
    have hge : lo ≤ detZ z' w := by
      rw [hh]; exact div_le_div_of_nonneg_right (by linarith) htz0.le
    have hle : (detZ z' w : ℝ) ≤ lo + 15 := by
      rw [hh]
      have : (tauR ω z' - j₁ * tauR ω w) / tauR ω z ≤ lo + 15 * P.U / ω.1 / tauR ω z := by
        rw [show lo + 15 * P.U / ω.1 / tauR ω z = (P.U / ω.1 - j₁ * tauR ω w + 15 * P.U / ω.1) /
          tauR ω z by simp only [lo]; field_simp]
        exact div_le_div_of_nonneg_right (by
          have : 16 * P.U / ω.1 = P.U / ω.1 + 15 * P.U / ω.1 := by ring
          linarith) htz0.le
      have h15 : 15 * P.U / ω.1 / tauR ω z ≤ 15 := by
        rw [div_le_iff₀ htz0]
        calc 15 * P.U / ω.1 = 15 * (P.U / ω.1) := by ring
          _ ≤ 15 * tauR ω z := by linarith
      linarith
    rw [mem_Icc]
    constructor
    · exact Int.ceil_le.2 hge
    · have : (detZ z' w : ℝ) ≤ ⌈lo⌉ + 15 := le_trans hle (by linarith [Int.le_ceil lo])
      exact_mod_cast this
  calc (P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = j₁)).card
      ≤ (Icc ⌈lo⌉ (⌈lo⌉ + 15)).card := by
        refine card_le_card_of_injOn (fun z' => detZ z' w) (fun z' hz' => hwin z' hz') ?_
        intro z' hz' z'' hz'' heq
        have h1 : detZ z z' = detZ z z'' := by
          rw [(mem_filter.1 hz').2.2, (mem_filter.1 hz'').2.2]
        exact eq_of_det_eq hz h1 heq
    _ = 16 := by simp only [Int.card_Icc]; omega

end Geo

/-! ## The kernel -/

lemma norm_minorKernel_le (x A₀ Y : ℝ) (t a b : ℤ) :
    ‖minorKernel x A₀ Y t a b‖ ≤ (if |(t : ℝ) / Y| < 5 then 1 else 0) *
      ((if t - b + a = 0 then 1 else 0) + (volume (majorArcs x A₀ Y)).toReal) := by
  rw [minorKernel_eq]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(arcCutoff (t / Y) : ℂ) * (if t - b + a = 0 then 1 else 0)‖ ≤
      (if |(t : ℝ) / Y| < 5 then 1 else 0) * (if t - b + a = 0 then 1 else 0) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul (abs_arcCutoff_le _) (by split_ifs <;> simp) (norm_nonneg _)
      (by split_ifs <;> norm_num)
  have h2 := norm_majorKernel_le x A₀ Y t a b
  rw [mul_add]
  linarith

lemma norm_edgeMult_le (P : MemParams) (j : ℕ) (t : ℤ) (a b D : ℕ) (hD : P.d₀ ≤ D) :
    ‖P.edgeMult j t a b D‖ ≤ (if |(t : ℝ) / P.Y| < 5 then 1 else 0) *
      ((if t = (b : ℤ) - a then 1 else 0) + (volume (majorArcs P.x P.A₀ P.Y)).toReal) := by
  unfold MemParams.edgeMult
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb0 := dyadicBump_nonneg ((b : ℝ) / P.Y)
  have ha0 := dyadicBump_nonneg ((a : ℝ) / P.Y)
  have hfac : |((P.d₀ : ℝ) / D) * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    have h1 : (P.d₀ : ℝ) / D ≤ 1 := by
      rcases Nat.eq_zero_or_pos D with h | h
      · simp [h]
      · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast hD
    have := dyadicBump_le_one ((b : ℝ) / P.Y)
    have := dyadicBump_le_one ((a : ℝ) / P.Y)
    have := dyadicBump_nonneg ((b : ℝ) / P.Y)
    have := dyadicBump_nonneg ((a : ℝ) / P.Y)
    have : (0 : ℝ) ≤ P.d₀ / D := by positivity
    calc (P.d₀ : ℝ) / D * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y) ≤ 1 * 1 * 1 := by
          gcongr
      _ = 1 := by ring
  have hk : ‖(if Even j then minorKernel P.x P.A₀ P.Y t a b
      else (starRingEnd ℂ) (minorKernel P.x P.A₀ P.Y (-t) b a))‖ ≤
      (if |(t : ℝ) / P.Y| < 5 then 1 else 0) *
        ((if t = (b : ℤ) - a then 1 else 0) + (volume (majorArcs P.x P.A₀ P.Y)).toReal) := by
    by_cases hj : Even j
    · rw [if_pos hj]
      refine (norm_minorKernel_le _ _ _ _ _ _).trans ?_
      have : (t - b + a = 0) ↔ (t = (b : ℤ) - a) := by omega
      simp only [this]; exact le_rfl
    · rw [if_neg hj, Complex.norm_conj]
      refine (norm_minorKernel_le _ _ _ _ _ _).trans ?_
      have e1 : |((-t : ℤ) : ℝ) / P.Y| = |(t : ℝ) / P.Y| := by push_cast; rw [neg_div, abs_neg]
      have e2 : (-t - a + b = 0) ↔ (t = (b : ℤ) - a) := by omega
      simp only [e1, e2]; exact le_rfl
  calc |((P.d₀ : ℝ) / D) * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y)| *
        ‖(if Even j then minorKernel P.x P.A₀ P.Y t a b
          else (starRingEnd ℂ) (minorKernel P.x P.A₀ P.Y (-t) b a))‖ ≤ 1 *
        ((if |(t : ℝ) / P.Y| < 5 then 1 else 0) *
        ((if t = (b : ℤ) - a then 1 else 0) + (volume (majorArcs P.x P.A₀ P.Y)).toReal)) :=
        mul_le_mul hfac hk (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-! ## The crude edge row -/

section Row

variable (P : MemParams)

/-- The kernel envelope `1[|t/Y| < 5] (1[t = b − a] + ε)`. -/
noncomputable def kEnv (ε : ℝ) (t : ℤ) (a b : ℕ) : ℝ :=
  (if |(t : ℝ) / P.Y| < 5 then 1 else 0) * ((if t = (b : ℤ) - a then 1 else 0) + ε)

lemma kEnv_nonneg {ε : ℝ} (hε : 0 ≤ ε) (t : ℤ) (a b : ℕ) : 0 ≤ kEnv P ε t a b := by
  unfold kEnv; split_ifs <;> positivity

lemma sum_kEnv_le (hY : 0 < P.Y) {ε : ℝ} (hε : 0 ≤ ε) (a b : ℕ) (T : Finset ℤ) :
    ∑ t ∈ T, kEnv P ε t a b ≤ 1 + (10 * P.Y + 1) * ε := by
  classical
  set M : ℤ := ⌊5 * P.Y⌋
  have hsupp : ∀ t ∈ T, t ∉ Icc (-M) M → kEnv P ε t a b = 0 := by
    intro t _ ht
    unfold kEnv
    rw [if_neg, zero_mul]
    intro h
    apply ht
    rw [abs_lt, lt_div_iff₀ hY, div_lt_iff₀ hY] at h
    rw [mem_Icc]
    constructor
    · have : -t ≤ M := Int.le_floor.2 (by push_cast; linarith)
      omega
    · exact Int.le_floor.2 (by linarith)
  calc ∑ t ∈ T, kEnv P ε t a b ≤ ∑ t ∈ T ∩ Icc (-M) M, kEnv P ε t a b := by
        rw [← sum_filter_add_sum_filter_not T (· ∈ Icc (-M) M)]
        rw [sum_eq_zero fun t ht => hsupp t (mem_filter.1 ht).1 (mem_filter.1 ht).2, add_zero,
          filter_mem_eq_inter]
    _ ≤ ∑ t ∈ Icc (-M) M, kEnv P ε t a b :=
        sum_le_sum_of_subset_of_nonneg inter_subset_right fun t _ _ => kEnv_nonneg P hε t a b
    _ ≤ ∑ t ∈ Icc (-M) M, ((if t = (b : ℤ) - a then 1 else 0) + ε) := by
        refine sum_le_sum fun t _ => ?_
        unfold kEnv
        have : 0 ≤ (if t = (b : ℤ) - a then (1 : ℝ) else 0) + ε := by split_ifs <;> positivity
        split_ifs <;> linarith
    _ ≤ 1 + (10 * P.Y + 1) * ε := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
        have h1 : ∑ t ∈ Icc (-M) M, (if t = (b : ℤ) - a then (1 : ℝ) else 0) ≤ 1 := by
          rw [sum_ite_eq']; split_ifs <;> norm_num
        have h2 : ((Icc (-M) M).card : ℝ) ≤ 10 * P.Y + 1 := by
          rw [Int.card_Icc]
          have hM0 : 0 ≤ M := Int.floor_nonneg.2 (by positivity)
          have : ((M + 1 - -M).toNat : ℝ) = 2 * M + 1 := by
            rw [show M + 1 - -M = 2 * M + 1 by ring]
            have : (0 : ℤ) ≤ 2 * M + 1 := by omega
            rw [← Int.cast_natCast, Int.toNat_of_nonneg this]; push_cast; ring
          rw [this]
          have : (M : ℝ) ≤ 5 * P.Y := Int.floor_le _
          linarith
        nlinarith

open Classical in
/-- The `z'`-sum of the kernel envelope: at most 16 targets per determinant. -/
lemma zsum_kEnv_le (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y) {ε : ℝ}
    (hε : 0 ≤ ε) {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) (hbox : P.InBox ω z) (D : ℕ) (hD : 0 < D)
    (a b : ℕ) :
    ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then kEnv P ε (detZ z z' / D) a b else 0)
      ≤ 16 * (1 + (10 * P.Y + 1) * ε) := by
  set g : ℤ × ℤ → ℤ := fun z' => detZ z z' / D
  rw [← sum_fiberwise_of_maps_to (s := P.zSet) (t := P.zSet.image g) (g := g)
    (fun z' hz' => mem_image_of_mem g hz')]
  have hfib : ∀ t ∈ P.zSet.image g, ∑ z' ∈ P.zSet.filter (fun z' => g z' = t),
      (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then kEnv P ε (detZ z z' / D) a b else 0) ≤
      16 * kEnv P ε t a b := by
    intro t _
    calc ∑ z' ∈ P.zSet.filter (fun z' => g z' = t),
          (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then kEnv P ε (detZ z z' / D) a b else 0)
        = ∑ z' ∈ (P.zSet.filter (fun z' => g z' = t)).filter
            (fun z' => P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z'), kEnv P ε (detZ z z' / D) a b :=
          (sum_filter _ _).symm
      _ = ∑ z' ∈ (P.zSet.filter (fun z' => g z' = t)).filter
            (fun z' => P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z'), kEnv P ε t a b := by
          refine sum_congr rfl fun z' hz' => ?_
          rw [show detZ z z' / D = t from (mem_filter.1 (mem_filter.1 hz').1).2]
      _ ≤ ∑ z' ∈ P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = D * t), kEnv P ε t a b := by
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => kEnv_nonneg P hε _ _ _)
          intro z' hz'
          simp only [mem_filter] at hz' ⊢
          obtain ⟨⟨hzz, hg⟩, hb, hd⟩ := hz'
          refine ⟨hzz, hb, ?_⟩
          rw [← hg]
          exact (Int.mul_ediv_cancel' hd).symm
      _ = (P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = D * t)).card * kEnv P ε t a b := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 16 * kEnv P ε t a b := by
          refine mul_le_mul_of_nonneg_right ?_ (kEnv_nonneg P hε _ _ _)
          exact_mod_cast target_count P ω hω hU hz hbox (D * t)
  calc ∑ t ∈ P.zSet.image g, ∑ z' ∈ P.zSet.filter (fun z' => g z' = t),
        (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then kEnv P ε (detZ z z' / D) a b else 0)
      ≤ ∑ t ∈ P.zSet.image g, 16 * kEnv P ε t a b := sum_le_sum hfib
    _ = 16 * ∑ t ∈ P.zSet.image g, kEnv P ε t a b := by rw [mul_sum]
    _ ≤ 16 * (1 + (10 * P.Y + 1) * ε) := by
        gcongr; exact sum_kEnv_le P hY hε a b _

end Row

section RowMain

variable (P : MemParams)

lemma lineOf_le {p : ℕ} (hp : 0 < p) (z : ℤ × ℤ) : lineOf p z ≤ p := by
  unfold lineOf
  split_ifs
  · exact le_rfl
  · have : NeZero p := ⟨hp.ne'⟩
    exact (ZMod.val_lt _).le

/-- The label weight of a target choice, uniform in the target position. -/
noncomputable def wBar (m : P.Mem) (i : Fin P.K) (x : ℕ × Bool) : ℝ :=
  if x.2 then (∑ l ∈ range (x.1 + 1), (P.memAt m (i, x.1, l) : ℝ)) / P.Vg i else P.nu i x.1

lemma wBar_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV : ∀ i, 0 < P.Vg i) (m : P.Mem)
    (i : Fin P.K) (x : ℕ × Bool) (hx : x.1 ∈ P.grp i) : 0 ≤ wBar P m i x := by
  unfold wBar; split_ifs
  · have := hV i; positivity
  · exact hnu i _ hx

lemma sum_memAt_le (m : P.Mem) (i : Fin P.K) :
    ∑ p ∈ P.grp i, ∑ l ∈ range (p + 1), (P.memAt m (i, p, l) : ℝ) ≤ P.memSize m := by
  classical
  have hmem : ∀ x : Fin P.K × ℕ × ℕ, (P.memAt m x : ℝ) =
      ∑ y : P.PT, if y.1 = x then (m y : ℝ) else 0 := by
    intro x
    unfold MemParams.memAt
    split_ifs with h
    · rw [sum_eq_single ⟨x, h⟩]
      · simp
      · intro y _ hy; rw [if_neg (fun h' => hy (Subtype.ext h'))]
      · simp
    · rw [Nat.cast_zero]; symm; refine sum_eq_zero fun y _ => ?_
      rw [if_neg]; intro h'; exact h (h' ▸ y.2)
  simp only [hmem]
  rw [sum_congr rfl fun p _ => sum_comm, sum_comm]
  unfold MemParams.memSize
  push_cast
  refine sum_le_sum fun y _ => ?_
  have h1 : ∀ p ∈ P.grp i, ∑ l ∈ range (p + 1), (if y.1 = (i, p, l) then (m y : ℝ) else 0) ≤
      if y.1.2.1 = p then (m y : ℝ) else 0 := by
    intro p _
    by_cases hp : y.1.2.1 = p
    · rw [if_pos hp]
      calc ∑ l ∈ range (p + 1), (if y.1 = (i, p, l) then (m y : ℝ) else 0)
          ≤ ∑ l ∈ range (p + 1), (if y.1.2.2 = l then (m y : ℝ) else 0) := by
            refine sum_le_sum fun l _ => ?_
            by_cases hl : y.1 = (i, p, l)
            · rw [if_pos hl, if_pos (by rw [hl])]
            · rw [if_neg hl]; split_ifs <;> positivity
        _ ≤ m y := by
            rw [sum_ite_eq]; split_ifs
            · exact le_rfl
            · positivity
    · refine le_of_eq_of_le (sum_eq_zero fun l _ => if_neg fun h => hp (by rw [h])) ?_
      rw [if_neg hp]
  calc ∑ p ∈ P.grp i, ∑ l ∈ range (p + 1), (if y.1 = (i, p, l) then (m y : ℝ) else 0)
      ≤ ∑ p ∈ P.grp i, (if y.1.2.1 = p then (m y : ℝ) else 0) := sum_le_sum h1
    _ ≤ m y := by
        rw [sum_ite_eq]; split_ifs
        · exact le_rfl
        · positivity

end RowMain

section RowThm

variable (P : MemParams)

lemma sum_storeCount_le (z : ℤ × ℤ) (ℓ : P.Lst) (St : Finset (Fin P.K)) :
    ∑ y : P.PT, P.storeCount z ℓ St y ≤ St.card := by
  classical
  unfold MemParams.storeCount
  simp only [card_filter]
  rw [sum_comm]
  calc ∑ i ∈ St, ∑ y : P.PT, (if P.storedPart z ℓ i = y.1 then 1 else 0)
      ≤ ∑ _i ∈ St, 1 := sum_le_sum fun i _ => by
        rw [← card_filter]
        exact card_le_one.2 fun a ha b hb =>
          Subtype.ext ((mem_filter.1 ha).2.symm.trans (mem_filter.1 hb).2)
    _ = St.card := by simp

lemma memSize_edgeOut_le (s : P.MState) (c : L102G.EC P) :
    P.memSize (P.edgeOutMem s c) ≤ P.memSize s.2.2 + c.1.card := by
  unfold MemParams.memSize MemParams.edgeOutMem
  calc ∑ y, (s.2.2 y - P.promCount c.2.1 c.2.2 y + P.storeCount s.1 s.2.1 c.1 y)
      ≤ ∑ y, (s.2.2 y + P.storeCount s.1 s.2.1 c.1 y) := sum_le_sum fun y _ => by omega
    _ = ∑ y, s.2.2 y + ∑ y, P.storeCount s.1 s.2.1 c.1 y := sum_add_distrib
    _ ≤ ∑ y, s.2.2 y + c.1.card := by
        have := sum_storeCount_le P s.1 s.2.1 c.1; omega

open Classical in
/-- The per-choice envelope of an edge coefficient. -/
lemma norm_coeffK_le (ω : ℝ × ℝ × ℝ) (κ : ℤ → ℕ → ℕ → ℕ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hκ : ∀ t a b D, P.d₀ ≤ D → ‖κ t a b D‖ ≤ kEnv P ε t a b)
    (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV : ∀ i, 0 < P.Vg i) (s : P.MState)
    (c : L102G.EC P) (hc : c ∈ P.edgeChoices) :
    ‖L102G.coeffK P κ ω s c‖ ≤
      (if P.InBox ω c.2.1 ∧ (padProd s.2.1 : ℤ) ∣ detZ s.1 c.2.1 then
        kEnv P ε (detZ s.1 c.2.1 / padProd s.2.1) (∏ i, (c.2.2 i).1) (lastProd s.2.1) else 0) *
      ∏ i, wBar P s.2.2 i (c.2.2 i) := by
  have htg : c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ univ :=
    tg_mem_of_mem_edgeChoices P hc
  have hgrp : ∀ i, (c.2.2 i).1 ∈ P.grp i := fun i =>
    (mem_product.1 (Fintype.mem_piFinset.1 htg i)).1
  have hW0 : ∀ i, 0 ≤ wBar P s.2.2 i (c.2.2 i) := fun i => wBar_nonneg P hnu hV _ i _ (hgrp i)
  unfold L102G.coeffK
  split_ifs with hE hB
  · obtain ⟨hOK, -, -, -⟩ := hE
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hρ : (0 : ℝ) ≤ memRho := by unfold memRho; norm_num
    have hρ1 : memRho ≤ 1 := by unfold memRho; norm_num
    have hfac : ∀ i, 0 ≤ (if (c.2.2 i).2 then
        (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) := by
      intro i; split_ifs
      · have := hV i; positivity
      · exact hnu i _ (hgrp i)
    have hrf0 : 0 ≤ L102G.rfac P s c := by
      unfold L102G.rfac
      exact mul_nonneg (mul_nonneg (pow_nonneg hρ _) (prod_nonneg fun i _ => hfac i))
        (pow_nonneg hρ _)
    rw [abs_of_nonneg hrf0]
    have hrf : L102G.rfac P s c ≤ ∏ i, wBar P s.2.2 i (c.2.2 i) := by
      unfold L102G.rfac
      have h1 : memRho ^ P.hitCount s.1 s.2.2 ≤ 1 := pow_le_one₀ hρ hρ1
      have h2 : memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c) ≤ 1 := pow_le_one₀ hρ hρ1
      have h3 : (∏ i, if (c.2.2 i).2 then
          (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) ≤
          ∏ i, wBar P s.2.2 i (c.2.2 i) := by
        refine prod_le_prod (fun i _ => hfac i) fun i _ => ?_
        unfold wBar
        split_ifs with hfl
        · have hVi := hV i
          refine div_le_div_of_nonneg_right ?_ hVi.le
          have hp0 : 0 < (c.2.2 i).1 := by
            have := hgrp i; simp only [MemParams.grp, primeGroup, mem_filter] at this
            exact this.2.1.pos
          have hl : lineOf (c.2.2 i).1 c.2.1 ∈ range ((c.2.2 i).1 + 1) :=
            mem_range.2 (Nat.lt_succ_of_le (lineOf_le hp0 _))
          unfold MemParams.promPart
          exact single_le_sum (f := fun l => (P.memAt s.2.2 (i, (c.2.2 i).1, l) : ℝ))
            (fun _ _ => by positivity) hl
        · exact le_rfl
      calc memRho ^ P.hitCount s.1 s.2.2 * (∏ i, if (c.2.2 i).2 then
            (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) *
            memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c) ≤ 1 * (∏ i, wBar P s.2.2 i (c.2.2 i)) * 1 := by
            have hP0 : 0 ≤ ∏ i, (if (c.2.2 i).2 then
                (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) :=
              prod_nonneg fun i _ => hfac i
            have hW : 0 ≤ ∏ i, wBar P s.2.2 i (c.2.2 i) := prod_nonneg fun i _ => hW0 i
            calc memRho ^ P.hitCount s.1 s.2.2 * (∏ i, if (c.2.2 i).2 then
                (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) *
                memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c) ≤
                1 * (∏ i, if (c.2.2 i).2 then
                (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) * 1 := by
                  apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hP0) h2 (by positivity)
                    (by positivity)
              _ ≤ 1 * (∏ i, wBar P s.2.2 i (c.2.2 i)) * 1 := by gcongr
        _ = ∏ i, wBar P s.2.2 i (c.2.2 i) := by ring
    have hk := hκ (detZ s.1 c.2.1 / padProd s.2.1) (∏ i, (c.2.2 i).1) (lastProd s.2.1)
      (padProd s.2.1) hOK.2.2.1
    rw [mul_comm]
    exact mul_le_mul hk hrf hrf0 (kEnv_nonneg P hε _ _ _)
  · exfalso; exact hB ⟨hE.1.2.2.2.2.2.2.1, hE.1.2.2.2.2.1⟩
  · rw [norm_zero]
    exact mul_nonneg (kEnv_nonneg P hε _ _ _) (prod_nonneg fun i _ => hW0 i)
  · rw [norm_zero, zero_mul]

end RowThm

section RowSum

variable (P : MemParams)

lemma sum_pow_card_univ {K : ℕ} (v₀ : ℝ) :
    ∑ St : Finset (Fin K), v₀ ^ St.card = (1 + v₀) ^ K := by
  have := Finset.sum_pow_mul_eq_add_pow v₀ 1 (univ : Finset (Fin K))
  simp only [one_pow, mul_one, card_univ, Fintype.card_fin, powerset_univ] at this
  rw [this, add_comm]

open Classical in
/-- **The crude edge row** ([21] (4.25)), weighted by `v₀^{memory}`, with the fresh labels of the
groups in `C` forced into `V`. -/
theorem edge_row (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y)
    (κ : ℤ → ℕ → ℕ → ℕ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hκ : ∀ t a b D, P.d₀ ≤ D → ‖κ t a b D‖ ≤ kEnv P ε t a b)
    (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV : ∀ i, 1 / 2 ≤ P.Vg i)
    (C : Finset (Fin P.K)) (Vs : Finset ℕ) {v₀ : ℝ} (hv₀ : 1 ≤ v₀) (s : P.MState)
    (hs : s ∈ P.stSet) :
    ∑ c ∈ P.edgeChoices, ‖L102G.coeffK P κ ω s c‖ *
      (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs then 1 else 0) *
        v₀ ^ P.memSize (P.edgeOutMem s c) ≤
    (1 + v₀) ^ P.K * (16 * (1 + (10 * P.Y + 1) * ε)) *
      (∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
        else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2)) * v₀ ^ P.memSize s.2.2 := by
  have hVpos : ∀ i, 0 < P.Vg i := fun i => by linarith [hV i]
  obtain ⟨hzs, hℓ, hm⟩ := (mem_stSet_iff' P s).1 hs
  have hzp : Int.gcd s.1.1 s.1.2 = 1 := by
    unfold MemParams.zSet at hzs; exact (mem_filter.1 hzs).2
  have hD : 0 < padProd s.2.1 := by
    unfold padProd
    simp only [listCands, Fintype.mem_piFinset] at hℓ
    exact prod_pos fun i _ => prod_pos fun k _ => by
      have := hℓ i k.castSucc; simp only [primeGroup, mem_filter] at this; exact this.2.1.pos
  have hRHS0 : 0 ≤ (1 + v₀) ^ P.K * (16 * (1 + (10 * P.Y + 1) * ε)) *
      (∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
        else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2)) * v₀ ^ P.memSize s.2.2 := by
    refine mul_nonneg (mul_nonneg (by positivity) (prod_nonneg fun i _ => ?_)) (by positivity)
    split_ifs
    · exact sum_nonneg fun p hp => hnu i p (mem_filter.1 hp).1
    · exact add_nonneg (sum_nonneg fun p hp => hnu i p hp) (by positivity)
  by_cases hbz : P.InBox ω s.1
  swap
  · refine le_trans (le_of_eq (sum_eq_zero fun c _ => ?_)) hRHS0
    unfold L102G.coeffK
    rw [if_neg (fun hE => hbz hE.1.2.2.2.2.2.1)]; simp
  set g : Fin P.K → ℕ × Bool → ℝ := fun i x => wBar P s.2.2 i x *
    (if (i ∈ C → (x.2 = false ∧ x.1 ∈ Vs)) then 1 else 0) with hg
  set E : (ℤ × ℤ) → (Fin P.K → ℕ × Bool) → ℝ := fun z' tg =>
    if P.InBox ω z' ∧ (padProd s.2.1 : ℤ) ∣ detZ s.1 z' then
      kEnv P ε (detZ s.1 z' / padProd s.2.1) (∏ i, (tg i).1) (lastProd s.2.1) else 0 with hE
  have hterm : ∀ c ∈ P.edgeChoices, ‖L102G.coeffK P κ ω s c‖ *
      (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs then 1 else 0) *
        v₀ ^ P.memSize (P.edgeOutMem s c) ≤
      v₀ ^ P.memSize s.2.2 * (v₀ ^ c.1.card * ((∏ i, g i (c.2.2 i)) * E c.2.1 c.2.2)) := by
    intro c hc
    have h1 := norm_coeffK_le P ω κ hε hκ hnu hVpos s c hc
    have hc2 : (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs then (1 : ℝ) else 0) =
        ∏ i, (if (i ∈ C → ((c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs)) then 1 else 0) := by
      rw [prod_boole]; simp
    have h3 : v₀ ^ P.memSize (P.edgeOutMem s c) ≤ v₀ ^ P.memSize s.2.2 * v₀ ^ c.1.card := by
      rw [← pow_add]; exact pow_le_pow_right₀ hv₀ (memSize_edgeOut_le P s c)
    have htg : c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ univ :=
      tg_mem_of_mem_edgeChoices P hc
    have hW0 : ∀ i, 0 ≤ wBar P s.2.2 i (c.2.2 i) := fun i => wBar_nonneg P hnu hVpos _ i _
      (mem_product.1 (Fintype.mem_piFinset.1 htg i)).1
    have hE0 : 0 ≤ E c.2.1 c.2.2 := by
      rw [hE]; dsimp only; split_ifs
      · exact kEnv_nonneg P hε _ _ _
      · exact le_rfl
    rw [hc2]
    calc ‖L102G.coeffK P κ ω s c‖ *
          (∏ i, (if (i ∈ C → ((c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs)) then (1 : ℝ) else 0)) *
          v₀ ^ P.memSize (P.edgeOutMem s c) ≤
        (E c.2.1 c.2.2 * ∏ i, wBar P s.2.2 i (c.2.2 i)) *
          (∏ i, (if (i ∈ C → ((c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs)) then (1 : ℝ) else 0)) *
          (v₀ ^ P.memSize s.2.2 * v₀ ^ c.1.card) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right h1 (prod_nonneg fun i _ => by
            split_ifs <;> norm_num)) h3 (by positivity) (mul_nonneg (mul_nonneg hE0
              (prod_nonneg fun i _ => hW0 i)) (prod_nonneg fun i _ => by split_ifs <;> norm_num))
      _ = v₀ ^ P.memSize s.2.2 * (v₀ ^ c.1.card * ((∏ i, g i (c.2.2 i)) * E c.2.1 c.2.2)) := by
          rw [hg]; dsimp only; rw [prod_mul_distrib]; ring
  refine (sum_le_sum hterm).trans ?_
  unfold MemParams.edgeChoices
  rw [sum_product]
  simp only [sum_product]
  rw [show (∑ St : Finset (Fin P.K), ∑ z' ∈ P.zSet,
      ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
        v₀ ^ P.memSize s.2.2 * (v₀ ^ St.card * ((∏ i, g i (tg i)) * E z' tg))) =
      v₀ ^ P.memSize s.2.2 * ((∑ St : Finset (Fin P.K), v₀ ^ St.card) *
        ∑ z' ∈ P.zSet, ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
          (∏ i, g i (tg i)) * E z' tg) by
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm.trans (sum_congr rfl fun _ _ => Finset.sum_comm)]
  -- the target and label sums
  have hzt : ∑ z' ∈ P.zSet, ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
      (∏ i, g i (tg i)) * E z' tg ≤ (16 * (1 + (10 * P.Y + 1) * ε)) *
        ∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
          else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2) := by
    rw [sum_comm]
    have hg0 : ∀ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
        0 ≤ ∏ i, g i (tg i) := by
      intro tg htg
      refine prod_nonneg fun i _ => mul_nonneg (wBar_nonneg P hnu hVpos _ i _
        (mem_product.1 (Fintype.mem_piFinset.1 htg i)).1) (by split_ifs <;> norm_num)
    calc ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
          ∑ z' ∈ P.zSet, (∏ i, g i (tg i)) * E z' tg
        = ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
          (∏ i, g i (tg i)) * ∑ z' ∈ P.zSet, E z' tg := by
          refine sum_congr rfl fun tg _ => by rw [mul_sum]
      _ ≤ ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
          (∏ i, g i (tg i)) * (16 * (1 + (10 * P.Y + 1) * ε)) :=
          sum_le_sum fun tg htg => mul_le_mul_of_nonneg_left
            (zsum_kEnv_le P ω hω hU hY hε hzp hbz _ hD _ _) (hg0 tg htg)
      _ = (16 * (1 + (10 * P.Y + 1) * ε)) * ∏ i, ∑ x ∈ P.grp i ×ˢ (univ : Finset Bool), g i x := by
          rw [← sum_mul, mul_comm, ← prod_univ_sum]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (prod_le_prod (fun i _ => sum_nonneg fun x hx =>
            mul_nonneg (wBar_nonneg P hnu hVpos _ i _ (mem_product.1 hx).1)
              (by split_ifs <;> norm_num)) fun i _ => ?_) (by positivity)
          rw [sum_product]
          simp only [Fintype.sum_bool]
          by_cases hiC : i ∈ C
          · rw [if_pos hiC, sum_filter]
            refine le_of_eq ?_
            refine sum_congr rfl fun p _ => ?_
            by_cases hp : p ∈ Vs
            · simp [hg, wBar, hiC, hp]
            · simp [hg, wBar, hiC, hp]
          · rw [if_neg hiC]
            simp only [hg, hiC, false_implies, if_true, mul_one, wBar, if_false, Bool.false_eq_true]
            rw [sum_add_distrib, add_comm]
            gcongr
            calc ∑ p ∈ P.grp i, (∑ l ∈ range (p + 1), (P.memAt s.2.2 (i, p, l) : ℝ)) / P.Vg i
                = (∑ p ∈ P.grp i, ∑ l ∈ range (p + 1), (P.memAt s.2.2 (i, p, l) : ℝ)) / P.Vg i := by
                  rw [sum_div]
              _ ≤ P.memSize s.2.2 / (1 / 2) := by
                  gcongr
                  all_goals first | exact hV i | exact sum_memAt_le P s.2.2 i | norm_num
              _ = 2 * P.memSize s.2.2 := by ring
  calc v₀ ^ P.memSize s.2.2 * ((∑ St : Finset (Fin P.K), v₀ ^ St.card) *
        ∑ z' ∈ P.zSet, ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
          (∏ i, g i (tg i)) * E z' tg)
      ≤ v₀ ^ P.memSize s.2.2 * ((1 + v₀) ^ P.K * ((16 * (1 + (10 * P.Y + 1) * ε)) *
        ∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
          else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2))) := by
        rw [sum_pow_card_univ]
        gcongr
    _ = _ := by ring

end RowSum

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the weighted Schur test for choice-indexed operators

An operator in the row convention, `(O f)(s) = ∑_{c ∈ Ch} coeff(s, c) f(out(s, c))` (outputs
outside the state set `St` dropped), on `ℓ²(St, μ)`. With a positive Schur weight `w`, a weighted
row bound `R` and a weighted column bound `C` give `‖O f‖² ≤ R C ‖f‖²` ([21] §4.4). -/

namespace ArtinPrimitiveRoots.L102D

open Finset

variable {α γ : Type*} [DecidableEq α]

/-- The choice-indexed operator. -/
def choiceOp (St : Finset α) (Ch : Finset γ) (coeff : α → γ → ℂ) (out : α → γ → α)
    (f : α → ℂ) (s : α) : ℂ :=
  ∑ c ∈ Ch, coeff s c * (if out s c ∈ St then f (out s c) else 0)

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the crude norm of a modified edge ([21] (4.23)–(4.25)) (for D7e)

An edge whose coefficients are multiplied by anything of modulus `≤ 1` (phases, validity checks) has
norm `≤ √R · √(3^K R)` on `H_B`, `R = 2^K · 16 (1 + (10Y+1) vol 𝔐) · (2 + 2B)^K`: rows by `edge_row`,
columns by prover G's reversal (`L102G.col_via_rev`), and G's bilinear Cauchy–Schwarz
(`L102G.piece_bound`, `L102G.opBound_of_bilin`). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory
open scoped ComplexConjugate

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- The crude edge row bound `R`. -/
noncomputable def edgeR : ℝ :=
  2 ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
    (2 + 2 * P.B) ^ P.K

lemma edgeR_nonneg (hY : 0 ≤ P.Y) : 0 ≤ edgeR P := by
  unfold edgeR
  have : (0 : ℝ) ≤ (volume (majorArcs P.x P.A₀ P.Y)).toReal := ENNReal.toReal_nonneg
  positivity

lemma kEnv_of_edgeMult (j : ℕ) (t : ℤ) (a b D : ℕ) (hD : P.d₀ ≤ D) :
    ‖P.edgeMult j t a b D‖ ≤ kEnv P (volume (majorArcs P.x P.A₀ P.Y)).toReal t a b := by
  have := norm_edgeMult_le P j t a b D hD
  unfold kEnv; exact this

lemma kEnv_of_edgeMult_rev (j : ℕ) (t : ℤ) (a b D : ℕ) (hD : P.d₀ ≤ D) :
    ‖P.edgeMult j (-t) b a D‖ ≤ kEnv P (volume (majorArcs P.x P.A₀ P.Y)).toReal t a b := by
  have := norm_edgeMult_le P j (-t) b a D hD
  unfold kEnv
  have e1 : |((-t : ℤ) : ℝ) / P.Y| = |(t : ℝ) / P.Y| := by
    push_cast; rw [neg_div, abs_neg]
  have e2 : (-t = (a : ℤ) - b) ↔ (t = (b : ℤ) - a) := by omega
  simp only [e1, e2] at this
  exact this

/-- The unweighted row bound of `coeffK` for a kernel with the `kEnv` envelope. -/
lemma coeffK_row_le (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y)
    (κ : ℤ → ℕ → ℕ → ℕ → ℂ)
    (hκ : ∀ t a b D, P.d₀ ≤ D →
      ‖κ t a b D‖ ≤ kEnv P (volume (majorArcs P.x P.A₀ P.Y)).toReal t a b)
    (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV : ∀ i, 1 / 2 ≤ P.Vg i)
    (hsum : ∀ i, ∑ p ∈ P.grp i, P.nu i p ≤ 2) (s : P.MState) (hs : s ∈ P.stSet) :
    ∑ c ∈ P.edgeChoices, ‖L102G.coeffK P κ ω s c‖ ≤ edgeR P := by
  have hε : (0 : ℝ) ≤ (volume (majorArcs P.x P.A₀ P.Y)).toReal := ENNReal.toReal_nonneg
  have h := edge_row P ω hω hU hY κ hε hκ hnu hV ∅ ∅ (le_refl (1 : ℝ)) s hs
  have e : ∀ c : L102G.EC P, (if ∀ i ∈ (∅ : Finset (Fin P.K)), (c.2.2 i).2 = false ∧
      (c.2.2 i).1 ∈ (∅ : Finset ℕ) then (1 : ℝ) else 0) = 1 := fun c => if_pos (by simp)
  simp only [e, mul_one, one_pow] at h
  refine h.trans ?_
  unfold edgeR
  have hm : P.memSize s.2.2 ≤ P.B := by
    have h1 := ((mem_stSet_iff' P s).1 hs).2.2
    unfold MemParams.memSet at h1
    exact (mem_filter.1 h1).2
  have hprod : ∏ i : Fin P.K, (∑ p ∈ P.grp i, P.nu i p + 2 * (P.memSize s.2.2 : ℝ)) ≤
      (2 + 2 * P.B) ^ P.K := by
    calc ∏ i : Fin P.K, (∑ p ∈ P.grp i, P.nu i p + 2 * (P.memSize s.2.2 : ℝ)) ≤
        ∏ _i : Fin P.K, (2 + 2 * (P.B : ℝ)) := by
          refine prod_le_prod (fun i _ => add_nonneg (sum_nonneg fun p hp => hnu i p hp)
            (by positivity)) fun i _ => ?_
          have : (P.memSize s.2.2 : ℝ) ≤ P.B := by exact_mod_cast hm
          linarith [hsum i]
      _ = _ := by rw [prod_const, card_univ, Fintype.card_fin]
  have h2 : (1 + 1 : ℝ) ^ P.K = 2 ^ P.K := by norm_num
  rw [h2]
  have h16 : 0 ≤ 16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal) := by
    have : 0 ≤ 10 * P.Y + 1 := by linarith
    positivity
  exact mul_le_mul_of_nonneg_left hprod (by positivity)

/-- **A modified edge** (coefficients dominated by `edgeCoeff`) has norm `≤ √R √(3^K R)`. -/
theorem edge_mod_opBound (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y)
    (j : ℕ) (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV1 : ∀ i, 1 / 2 ≤ P.Vg i)
    (hV2 : ∀ i, P.Vg i ≤ 3 / 2) (hsum : ∀ i, ∑ p ∈ P.grp i, P.nu i p ≤ 2)
    (cf : P.MState → L102G.EC P → ℂ) (hcf : ∀ s c, ‖cf s c‖ ≤ ‖P.edgeCoeff ω j s c‖) :
    P.OpBound (choiceOp P.stSet P.edgeChoices cf P.edgeOut)
      (√(edgeR P) * √(3 ^ P.K * edgeR P)) := by
  classical
  have hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s := fun s hs => L102G.stWeight_nonneg P hnu s hs
  set R := edgeR P
  have hR : 0 ≤ R := edgeR_nonneg P hY.le
  set κ' : ℤ → ℕ → ℕ → ℕ → ℂ := fun t a b D => P.edgeMult j (-t) b a D
  have hcfK : ∀ s c, ‖cf s c‖ ≤ ‖L102G.coeffP P (fun _ _ => True) (P.edgeMult j) ω s c‖ := by
    intro s c
    unfold L102G.coeffP
    rw [if_pos trivial, ← L102G.edgeCoeff_eq]
    exact hcf s c
  have hrow1 : ∀ s ∈ P.stSet, ∑ c ∈ P.edgeChoices, ‖cf s c‖ ≤ R := by
    intro s hs
    refine (sum_le_sum fun c _ => hcf s c).trans ?_
    simp only [L102G.edgeCoeff_eq]
    exact coeffK_row_le P ω hω hU hY _ (fun t a b D hD => kEnv_of_edgeMult P j t a b D hD)
      hnu hV1 hsum s hs
  have hrow2 : ∀ s ∈ P.stSet, ∑ c ∈ P.edgeChoices,
      ‖L102G.coeffP P (fun _ _ => True) κ' ω s c‖ ≤ R := by
    intro s hs
    unfold L102G.coeffP
    simp only [if_true]
    exact coeffK_row_le P ω hω hU hY κ' (fun t a b D hD => kEnv_of_edgeMult_rev P j t a b D hD)
      hnu hV1 hsum s hs
  refine L102G.opBound_of_bilin P _ _ (by positivity) hμ fun g f => ?_
  have hpb := L102G.piece_bound P P.edgeChoices cf P.edgeOut g f R (3 ^ P.K * R) hμ ?_ ?_
  · unfold L102G.ipμ choiceOp
    exact hpb
  · -- rows
    rw [mul_sum]
    refine sum_le_sum fun s hs => ?_
    have h0 := hμ s hs
    calc ∑ c ∈ P.edgeChoices, P.stWeight s * ‖cf s c‖ *
          (if P.edgeOut s c ∈ P.stSet then (1 : ℝ) else 0) * ‖g s‖ ^ 2 ≤
        ∑ c ∈ P.edgeChoices, ‖cf s c‖ * (P.stWeight s * ‖g s‖ ^ 2) :=
          sum_le_sum fun c _ => by
            have := norm_nonneg (cf s c)
            split_ifs
            · nlinarith [sq_nonneg ‖g s‖]
            · simp only [mul_zero, zero_mul]; positivity
      _ = (∑ c ∈ P.edgeChoices, ‖cf s c‖) * (P.stWeight s * ‖g s‖ ^ 2) := by rw [sum_mul]
      _ ≤ R * (P.stWeight s * ‖g s‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (hrow1 s hs) (by positivity)
  · -- columns
    have hcol := L102G.col_via_rev P (fun _ _ => True) (fun _ _ => True) (fun _ _ _ => trivial)
      (P.edgeMult j) κ' (fun t a b D => by simp only [κ', neg_neg]; exact le_refl _) ω hnu hV1
      hV2 (fun s => ‖f s‖ ^ 2) (fun s => sq_nonneg _)
    calc ∑ s ∈ P.stSet, ∑ c ∈ P.edgeChoices, P.stWeight s * ‖cf s c‖ *
          (if P.edgeOut s c ∈ P.stSet then ‖f (P.edgeOut s c)‖ ^ 2 else 0) ≤
        ∑ s ∈ P.stSet, ∑ c ∈ P.edgeChoices,
          P.stWeight s * ‖L102G.coeffP P (fun _ _ => True) (P.edgeMult j) ω s c‖ *
          (if P.edgeOut s c ∈ P.stSet then ‖f (P.edgeOut s c)‖ ^ 2 else 0) := by
          refine sum_le_sum fun s hs => sum_le_sum fun c _ => ?_
          have h0 := hμ s hs
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcfK s c) h0)
            (by split_ifs <;> positivity)
      _ ≤ 3 ^ P.K * ∑ s' ∈ P.stSet, ‖f s'‖ ^ 2 * ∑ c' ∈ P.edgeChoices,
          P.stWeight s' * ‖L102G.coeffP P (fun _ _ => True) κ' ω s' c'‖ := hcol
      _ ≤ 3 ^ P.K * ∑ s' ∈ P.stSet, ‖f s'‖ ^ 2 * (P.stWeight s' * R) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun s hs => ?_) (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (hrow2 s hs) (hμ s hs)
      _ = 3 ^ P.K * R * ∑ s ∈ P.stSet, P.stWeight s * ‖f s‖ ^ 2 := by
          simp only [mul_sum]
          exact sum_congr rfl fun s _ => by ring

end ArtinPrimitiveRoots.L102D
end

section
/-! Check module: `chk_opBound_edge_of_norm_le_edgeCoeff`, the published statement `opBound_edge_of_norm_le_edgeCoeff` verbatim, proved from the
development. -/

namespace ArtinPrimitiveRoots

open Finset MeasureTheory

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Finset MeasureTheory
theorem solution (P : MemParams) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω)
    (hU : 0 < P.U) (hY : 0 < P.Y) (j : ℕ) (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p)
    (hV1 : ∀ i, 1 / 2 ≤ P.Vg i) (hV2 : ∀ i, P.Vg i ≤ 3 / 2)
    (hsum : ∀ i, ∑ p ∈ P.grp i, P.nu i p ≤ 2)
    (cf : P.MState → Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool) → ℂ)
    (hcf : ∀ s c, ‖cf s c‖ ≤ ‖P.edgeCoeff ω j s c‖) :
    P.OpBound (fun f s => ∑ c ∈ P.edgeChoices,
      cf s c * (if P.edgeOut s c ∈ P.stSet then f (P.edgeOut s c) else 0))
      (√(2 ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
          (2 + 2 * P.B) ^ P.K) *
        √(3 ^ P.K * (2 ^ P.K * (16 * (1 + (10 * P.Y + 1) *
          (volume (majorArcs P.x P.A₀ P.Y)).toReal)) * (2 + 2 * P.B) ^ P.K))) :=
  L102D.edge_mod_opBound P ω hω hU hY j hnu hV1 hV2 hsum cf hcf
end
