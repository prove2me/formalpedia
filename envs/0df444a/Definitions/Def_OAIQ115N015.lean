-- Prove2me | Definitions.Def_OAIQ115N015
-- name    : OAIQ115N015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:13:19.297814+00:00
-- url     : https://prove2.me/theorems/90b8bbf0-7128-40ba-92e2-a825afd2d380
-- title:
--   Definitions bundle OAIQ115N015 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 78 declarations of OpenAI's Lean: 11 definitions, 2 instances and 65 theorems. The definitions and types are `OAI.NaimarkZFC.CAR`, `OAI.NaimarkZFC.PeakingPairData.pureIndex`, `OAI.NaimarkZFC.PeakingPairData.tail`, `OAI.NaimarkZFC.PureStateEquivalent`, `OAI.NaimarkZFC.PureUEP`, `OAI.NaimarkZFC.StateExtensionUnique`, `OAI.NaimarkZFC.bridgeWordSet`, `OAI.NaimarkZFC.bridgeWordSpan`, `OAI.NaimarkZFC.carInclude`, `OAI.NaimarkZFC.cstarDirectLimitState`, `OAI.NaimarkZFC.directLimitFunctional`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_CAR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/CAR.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Peaking`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Peaking.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N012` and `OAIQ115N013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N017`, `OAIQ115N018`, `OAIQ115N019` and `OAIQ115N020`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N012
import Definitions.Def_OAIQ115N013

section
-- module Solutions.OAIQ115_Naimark.Naimark_Peaking
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_isClosed _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

section
open scoped CStarAlgebra
variable {A B Z : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra Z]

variable (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)

variable (ψ : CStarMatrix Bool Bool B →⋆ₐ[ℂ] Z)
  (diag : ∀ i : Bool, φ (matrixSingle i i (1 : A)) = ψ (matrixSingle i i (1 : B)))

variable (δ : Bool → B →⋆ₐ[ℂ] A)
  (hδ : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ B) x))

include hδ in

theorem matrixStable_conjugates (b : B) :
    matrixStable φ ψ (matrixDiagonal_units φ ψ δ hδ) * matrixCornerBase φ (δ false b) *
      star (matrixStable φ ψ (matrixDiagonal_units φ ψ δ hδ)) =
    matrixCornerBase φ (δ true b) := by
  apply Subtype.ext
  change (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) *
    φ (matrixSingle false false (δ false b)) *
    star (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) =
    φ (matrixSingle false false (δ true b))
  simp only [star_mul, ← map_star, matrixSingle_star, star_one]
  rw [matrixDiagonal_agrees φ ψ δ hδ false b]
  calc
    _ = φ (matrixSingle false true (1 : A)) *
      (ψ (matrixSingle true false (1 : B)) * ψ (matrixSingle false false b) *
        ψ (matrixSingle false true (1 : B))) * φ (matrixSingle true false (1 : A)) := by
      simp only [mul_assoc]
    _ = φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true true b) *
        φ (matrixSingle true false (1 : A)) := by
      rw [← map_mul, matrixSingle_mul, one_mul, ← map_mul, matrixSingle_mul, mul_one]
    _ = _ := by
      rw [← matrixDiagonal_agrees φ ψ δ hδ true b,
        ← map_mul, matrixSingle_mul, one_mul, ← map_mul, matrixSingle_mul, mul_one]

end

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint
section
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
theorem matrixTraceState_tracial (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (M N : CStarMatrix n n A) :
    matrixTraceState τ hτ (M*N) = matrixTraceState τ hτ (N*M) :=
  normalizedMatrixTrace_tracial (positiveOfSquares τ hτ.2) htr M N

theorem matrix_cornerState (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (i : n) (q : A)
    (M : CStarMatrix n n A) :
    cornerState (matrixTraceState τ hτ) (matrixSingle i i q) M = cornerState τ q (M i i) := by
  rw [cornerState_apply,cornerState_apply,matrixSingle_compress,
    matrixTraceState_single,matrixTraceState_single,Complex.smul_re,smul_eq_mul,
    mul_inv_rev,smul_smul]
  have hc : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  congr 1
  rw [mul_assoc, inv_inv, mul_inv_cancel₀ hc,mul_one]

variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
  (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ k, 0 < (τ (peakAtom p k)).re)

include hpos in
theorem matrix_peakAtom_positive (i : n) (k : ℕ) :
    0 < (matrixTraceState τ hτ (peakAtom (fun m => matrixSingle i i (p m)) k)).re := by
  rw [matrix_peakAtom,matrixTraceState_single,Complex.smul_re,smul_eq_mul]
  exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)) (hpos k)

end

open Filter Topology
open scoped ComplexOrder

open Filter Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Filter Topology
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Peaks.rectangular_excision {p : ℕ → A} {f : A →L[ℂ] ℂ}
    (hp : Peaks p f) (a : A) (ha : f a = 0) :
    Tendsto (fun nt : ℕ × ℕ => p nt.1*a*p nt.2) atTop (𝓝 0) := by
  have hmin : Tendsto (fun nt : ℕ × ℕ => min nt.1 nt.2) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact eventually_atTop.2 ⟨(n,n), fun _ h => le_min h.1 h.2⟩
  have hc : Tendsto (fun n => ‖p n*a*p n‖) atTop (𝓝 0) := by
    simpa only [ha,zero_smul,sub_zero] using hp.excision a
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (g := fun nt : ℕ × ℕ => ‖p (min nt.1 nt.2)*a*p (min nt.1 nt.2)‖) ?_ (hc.comp hmin)
  intro nt
  let q := min nt.1 nt.2
  have he : p nt.1*(p q*a*p q)*p nt.2 = p nt.1*a*p nt.2 := by
    calc
      _ = (p nt.1*p q)*a*(p q*p nt.2) := by simp only [mul_assoc]
      _ = _ := by rw [hp.mul_peak,hp.mul_peak,max_eq_left (min_le_left _ _),
        max_eq_right (min_le_right _ _)]
  rw [← he]
  calc
    _ ≤ ‖p nt.1‖*‖p q*a*p q‖*‖p nt.2‖ := norm_mul₃_le
    _ ≤ 1*‖p q*a*p q‖*1 := by gcongr <;> exact (hp.1 _).norm_le _
    _ = _ := by rw [one_mul,mul_one]

end

open Filter Topology

section
variable {F B : Type*} [CStarAlgebra F] [CStarAlgebra B]
  (φ : F →⋆ₐ[ℂ] B) (b : Bool → B) (K : F → Prop)

def bridgeWordSet : Set B := Set.range φ ∪
  {z | ∃ (w : BridgeCore F) (a c : F), w.Centered K ∧ z = φ a*w.eval φ b*φ c}

def bridgeWordSpan : Submodule ℂ B := Submodule.span ℂ (bridgeWordSet φ b K)

theorem bridgeWordSpan_base (a : F) : φ a ∈ bridgeWordSpan φ b K :=
  Submodule.subset_span (Or.inl ⟨a,rfl⟩)

theorem bridgeWordSpan_word (w : BridgeCore F) (a c : F) (hw : w.Centered K) :
    φ a*w.eval φ b*φ c ∈ bridgeWordSpan φ b K :=
  Submodule.subset_span (Or.inr ⟨w,a,c,hw,rfl⟩)

theorem bridgeWordSpan_mul_base (a : F) {z : B} (hz : z ∈ bridgeWordSpan φ b K) :
    φ a*z ∈ bridgeWordSpan φ b K := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨c,rfl⟩ | ⟨w,c,d,hw,rfl⟩
    · simpa only [← map_mul] using bridgeWordSpan_base φ b K (a*c)
    · simpa only [map_mul,mul_assoc] using bridgeWordSpan_word φ b K w (a*c) d hw
  | zero => simpa only [mul_zero] using (bridgeWordSpan φ b K).zero_mem
  | add x y hx hy ix iy => simpa only [mul_add] using (bridgeWordSpan φ b K).add_mem ix iy
  | smul c z hz iz => simpa only [mul_smul_comm] using (bridgeWordSpan φ b K).smul_mem c iz

theorem bridgeWordSpan_mul_base_right (a : F) {z : B} (hz : z ∈ bridgeWordSpan φ b K) :
    z*φ a ∈ bridgeWordSpan φ b K := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨c,rfl⟩ | ⟨w,c,d,hw,rfl⟩
    · simpa only [← map_mul] using bridgeWordSpan_base φ b K (c*a)
    · simpa only [map_mul,mul_assoc] using bridgeWordSpan_word φ b K w c (d*a) hw
  | zero => simpa only [zero_mul] using (bridgeWordSpan φ b K).zero_mem
  | add x y hx hy ix iy => simpa only [add_mul] using (bridgeWordSpan φ b K).add_mem ix iy
  | smul c z hz iz => simpa only [smul_mul_assoc] using (bridgeWordSpan φ b K).smul_mem c iz

variable (center : F → F) (hc : ∀ a, K (center a)) (r : Bool → F → Bool → F)
  (hr : ∀ i a j, b i*φ a*b j = b i*φ (center a)*b j + φ (r i a j))
include hc hr

theorem bridgeWordSpan_left_word (i : Bool) (w : BridgeCore F) (a c : F)
    (hw : w.Centered K) : b i*(φ a*w.eval φ b*φ c) ∈ bridgeWordSpan φ b K := by
  have hmain := bridgeWordSpan_word φ b K (w.cons i (center a)) 1 c
    (w.centered_cons K i (center a) (hc a) hw)
  simp only [map_one,one_mul,BridgeCore.eval_cons] at hmain
  cases w with
  | single j =>
    have he : b i*(φ a*b j*φ c) = (b i*φ (center a)*b j*φ c) + φ (r i a j)*φ c := by
      rw [← mul_assoc (b i),← mul_assoc (b i),hr,add_mul]
    rw [BridgeCore.eval,he]
    exact (bridgeWordSpan φ b K).add_mem hmain
      (bridgeWordSpan_mul_base_right φ b K c (bridgeWordSpan_base φ b K _))
  | double j d k =>
    have he : b i*(φ a*(b j*φ d*b k)*φ c) =
        b i*φ (center a)*(b j*φ d*b k)*φ c + φ (r i a j*d)*b k*φ c := by
      calc
        _ = (b i*φ a*b j)*φ d*b k*φ c := by simp only [mul_assoc]
        _ = _ := by rw [hr]; simp only [add_mul,map_mul,mul_assoc]
    rw [BridgeCore.eval,he]
    exact (bridgeWordSpan φ b K).add_mem hmain
      (bridgeWordSpan_word φ b K (.single k) (r i a j*d) c trivial)
  | flank j d w e k =>
    have he : b i*(φ a*(b j*φ d*w.eval φ b*φ e*b k)*φ c) =
        b i*φ (center a)*(b j*φ d*w.eval φ b*φ e*b k)*φ c +
          φ (r i a j*d)*(w.snoc e k).eval φ b*φ c := by
      calc
        _ = (b i*φ a*b j)*φ d*w.eval φ b*φ e*b k*φ c := by simp only [mul_assoc]
        _ = _ := by rw [hr]; simp only [add_mul,map_mul,mul_assoc,BridgeCore.eval_snoc]
    rw [BridgeCore.eval,he]
    exact (bridgeWordSpan φ b K).add_mem hmain
      (bridgeWordSpan_word φ b K (w.snoc e k) (r i a j*d) c
        (w.centered_snoc K e k hw.2.2 hw.2.1))

theorem bridgeWordSpan_mul_letter (i : Bool) {z : B} (hz : z ∈ bridgeWordSpan φ b K) :
    b i*z ∈ bridgeWordSpan φ b K := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨a,rfl⟩ | ⟨w,a,c,hw,rfl⟩
    · simpa only [map_one,one_mul,BridgeCore.eval] using
        bridgeWordSpan_word φ b K (.single i) 1 a trivial
    · exact bridgeWordSpan_left_word φ b K center hc r hr i w a c hw
  | zero => simpa only [mul_zero] using (bridgeWordSpan φ b K).zero_mem
  | add x y hx hy ix iy => simpa only [mul_add] using (bridgeWordSpan φ b K).add_mem ix iy
  | smul c z hz iz => simpa only [mul_smul_comm] using (bridgeWordSpan φ b K).smul_mem c iz

theorem adjoin_le_bridgeWordSpan :
    (Algebra.adjoin ℂ (Set.range φ ∪ Set.range b)).toSubmodule ≤ bridgeWordSpan φ b K := by
  intro z hz
  have hinv : ∀ x ∈ Algebra.adjoin ℂ (Set.range φ ∪ Set.range b),
      ∀ y ∈ bridgeWordSpan φ b K, x*y ∈ bridgeWordSpan φ b K := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨a,rfl⟩ | ⟨i,rfl⟩
      · exact fun y hy => bridgeWordSpan_mul_base φ b K a hy
      · exact fun y hy => bridgeWordSpan_mul_letter φ b K center hc r hr i hy
    | algebraMap s =>
      intro y hy
      simpa only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul] using
        (bridgeWordSpan φ b K).smul_mem s hy
    | add x y hx hy ix iy =>
      intro z hz
      simpa only [add_mul] using (bridgeWordSpan φ b K).add_mem (ix z hz) (iy z hz)
    | mul x y hx hy ix iy =>
      intro z hz
      simpa only [mul_assoc] using ix (y*z) (iy z hz)
  have h1 : (1:B) ∈ bridgeWordSpan φ b K := by
    simpa only [map_one] using bridgeWordSpan_base φ b K 1
  simpa only [mul_one] using hinv z hz 1 h1

end

section
open scoped CStarAlgebra
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
  [PartialOrder A] [StarOrderedRing A]
  [PartialOrder D] [StarOrderedRing D]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)
  (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
  (δ : Bool → D →⋆ₐ[ℂ] A)
  (hd : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x))

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in

theorem bridgeLetter_transfer (g : D) (i : Bool) :
    φ (matrixSingle i i (δ i g))*bridgeLetter ψ i =
      bridgeLetter ψ i*φ (matrixSingle (!i) (!i) (δ (!i) g)) := by
  rw [matrixDiagonal_agrees φ ψ δ hd,matrixDiagonal_agrees φ ψ δ hd,
    bridgeLetter,← map_mul,← map_mul,matrixSingle_mul,matrixSingle_mul,mul_one,one_mul]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem matrixSingle_diagonal_general (x : Bool → D) (i j : Bool) (a : A) :
    matrixSingle i j a * matrixDiagonalHom δ x = matrixSingle i j (a * δ j (x j)) := by
  ext k l
  change (Matrix.single i j a * Matrix.diagonal (fun v => δ v (x v))) k l = _
  rw [Matrix.mul_diagonal]
  by_cases h : i = k ∧ j = l
  · rcases h with ⟨rfl,rfl⟩; simp
  · simp [matrixSingle_apply,h]

omit [PartialOrder D] [StarOrderedRing D] in

theorem matrix_offdiagonal_turn (x : Bool → D) (i j : Bool) :
    matrixSingle i (!i) (1:D) * matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x *
      matrixSingle j (!j) 1 =
    matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D)
      (Pi.single i (if j = !i then x (!i) else 0)) := by
  rw [matrixSingle_diagonal_general]
  simp only [StarAlgHom.coe_id, id_eq, one_mul]
  by_cases h : j = !i
  · subst j
    rw [ite_eq_left rfl,matrixSingle_mul,Bool.not_not,mul_one,matrixDiagonalHom_single]
    rfl
  · rw [matrixSingle_mul_of_ne _ _ _ _ _ _ (Ne.symm h),ite_eq_right h,Pi.single_zero,map_zero]

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in

theorem bridgeLetter_diagonal_turn (x : Bool → D) (i j : Bool) :
    bridgeLetter ψ i * φ (matrixDiagonalHom δ x) * bridgeLetter ψ j =
      φ (matrixDiagonalHom δ (Pi.single i (if j = !i then x (!i) else 0))) := by
  rw [hd,bridgeLetter,bridgeLetter,← map_mul,← map_mul,matrix_offdiagonal_turn,← hd]

variable (E : CStarMatrix Bool Bool A →L[ℂ] (Bool → D))
  (hE : ∀ x, E (matrixDiagonalHom δ x) = x)

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem bridgeLetter_turn (i : Bool) (a : CStarMatrix Bool Bool A) (j : Bool) :
    bridgeLetter ψ i * φ a * bridgeLetter ψ j =
      bridgeLetter ψ i * φ (bridgeCenter δ E a) * bridgeLetter ψ j +
        φ (matrixDiagonalHom δ (Pi.single i (if j = !i then (E a) (!i) else 0))) := by
  rw [bridgeCenter,map_sub,mul_sub,sub_mul,bridgeLetter_diagonal_turn φ ψ δ hd]
  exact (sub_add_cancel _ _).symm

include hd hE in
omit [PartialOrder D] [StarOrderedRing D] in

theorem matrix_bridge_adjoin_le_span :
    (Algebra.adjoin ℂ (Set.range φ ∪ Set.range (bridgeLetter ψ))).toSubmodule ≤
      bridgeWordSpan φ (bridgeLetter ψ) (fun a => E a = 0) := by
  exact adjoin_le_bridgeWordSpan φ (bridgeLetter ψ) (fun a => E a = 0)
    (bridgeCenter δ E) (bridgeCenter_centered δ E hE)
    (fun i a j => matrixDiagonalHom δ (Pi.single i (if j = !i then (E a) (!i) else 0)))
    (bridgeLetter_turn φ ψ δ hd E)

end

open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra
section
variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
  (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)

theorem peakingCoefficients_peak_nat (m n : ℕ) :
    peakingCoefficients hp τ hτ hpos (p n) m = if m < n then 0 else 1 := by
  rw [peakingCoefficients_nat]
  by_cases h : m < n
  · rw [ite_eq_left h,cornerState_apply,hp.peakAtom_mul_peak h,zero_mul,map_zero,smul_zero]
  · rw [ite_eq_right h]
    exact cornerState_eq_one τ hτ _ _ (hp.peakAtom_projection m) (hp.1 n)
      ((hp.peakAtom_le m).trans (hp.2.1 (Nat.le_of_not_gt h))) (hpos m)

theorem peakingCoefficients_peak_eq
    {q : ℕ → B} {g : B →L[ℂ] ℂ} (hq : Peaks q g)
    (σ : B →L[ℂ] ℂ) (hσ : IsState σ) (hposq : ∀ n, 0 < (σ (peakAtom q n)).re) (n : ℕ) :
    peakingCoefficients hp τ hτ hpos (p n) = peakingCoefficients hq σ hσ hposq (q n) := by
  ext x
  induction x using OnePoint.rec with
  | infty => rw [peakingCoefficients_infty,peakingCoefficients_infty,hp.2.2.2.1,hq.2.2.2.1]
  | coe m => rw [peakingCoefficients_peak_nat,peakingCoefficients_peak_nat]

include τ hτ hpos in

theorem sequenceDiagonalHom_matched_peak (hp0 : p 0 = 1)
    (d : AtomicTraceData A ℕ) (hd : ∀ m, (d.atom m).1 = peakAtom p m)
    {q : ℕ → B} {g : B →L[ℂ] ℂ} (hq : Peaks q g)
    (σ : B →L[ℂ] ℂ) (hσ : IsState σ) (hposq : ∀ m, 0 < (σ (peakAtom q m)).re) (n : ℕ) :
    sequenceDiagonalHom hp d hd (peakingCoefficients hq σ hσ hposq (q n)) = p n := by
  rw [← peakingCoefficients_peak_eq hp τ hτ hpos hq σ hσ hposq n,
    sequenceDiagonalHom_peakingCoefficients hp hp0,peakingExpectation_peak hp hp0]

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

attribute [local instance] OAI.NaimarkZFC.PeakingPairData.matrixFamilyStarOrder
theorem expectation_fixes (x : Bool → SequenceDiagonal) :
    B.expectation (matrixDiagonalHom B.diagonal x) = x := B.amalgam.fix false x

theorem letter_centered (i : Bool) :
    B.amalgam.expectation true (matrixSingle i (!i) (1:SequenceDiagonal)) = 0 := by
  ext j x
  change (matrixDiagonalExpectation (B.input true).expectation (B.input true).bound
    (matrixSingle i (!i) (1:SequenceDiagonal))) j x = 0
  rw [matrixDiagonalExpectation_apply]
  have hn : ¬ (i = j ∧ (!i) = j) := by cases i <;> cases j <;> simp
  rw [matrixSingle_apply,ite_eq_right hn,map_zero]
  rfl

def tail (n : ℕ) : SequenceDiagonal :=
  peakingCoefficients (B.peaks false) (positiveCLM B.trace)
    (positiveCLM_isState B.trace B.normalized) (B.atom_positive false) (B.peak false n)

theorem diagonal_tail (i : Bool) (n : ℕ) : B.diagonal i (B.tail n) = B.peak i n := by
  exact sequenceDiagonalHom_matched_peak (B.peaks i) (positiveCLM B.trace)
    (positiveCLM_isState B.trace B.normalized) (B.atom_positive i) (B.peak_zero i)
    (peakAtomicTraceData (B.peaks i) (B.peak_zero i) B.trace B.tracial B.normalized
      B.faithful (B.atom_positive i) (B.trace_null i)) (fun _ => rfl)
    (B.peaks false) (positiveCLM B.trace) (positiveCLM_isState B.trace B.normalized)
    (B.atom_positive false) n

theorem peak_transfer (i : Bool) (n : ℕ) :
    B.base (B.matrixPeak i n)*B.letter i = B.letter i*B.base (B.matrixPeak (!i) n) := by
  simpa only [B.diagonal_tail,matrixPeak] using
    bridgeLetter_transfer B.base B.aux B.diagonal B.diagonal_agree (B.tail n) i

end PeakingPairData

section
open scoped CStarAlgebra
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)
  (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
  (δ : Bool → D →⋆ₐ[ℂ] A)
  (hd : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x))

omit [PartialOrder D] [StarOrderedRing D] in
theorem matrix_eq_sum_entries (M : CStarMatrix Bool Bool D) :
    M = ∑ i : Bool, ∑ j : Bool, matrixSingle i j (M i j) := by
  change CStarMatrix.ofMatrix.symm M = ∑ i : Bool, ∑ j : Bool, Matrix.single i j (M i j)
  exact Matrix.matrix_eq_sum_single _

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in

theorem matrixAux_mem_adjoin (M : CStarMatrix Bool Bool D) :
    ψ M ∈ Algebra.adjoin ℂ (Set.range φ ∪ Set.range (bridgeLetter ψ)) := by
  let S := Algebra.adjoin ℂ (Set.range φ ∪ Set.range (bridgeLetter ψ))
  have hdiag (i : Bool) (a : D) : ψ (matrixSingle i i a) ∈ S := by
    rw [← matrixDiagonal_agrees φ ψ δ hd]
    exact Algebra.subset_adjoin (Or.inl ⟨_,rfl⟩)
  have hoff (i : Bool) (a : D) : ψ (matrixSingle i (!i) a) ∈ S := by
    have he : ψ (matrixSingle i (!i) a) =
        ψ (matrixSingle i i a)*bridgeLetter ψ i := by
      rw [bridgeLetter,← map_mul,matrixSingle_mul,mul_one]
    rw [he]
    exact S.mul_mem (hdiag i a) (Algebra.subset_adjoin (Or.inr ⟨i,rfl⟩))
  rw [matrix_eq_sum_entries M,map_sum]
  apply S.sum_mem
  intro i _
  rw [map_sum]
  apply S.sum_mem
  intro j _
  by_cases h : j = i
  · subst j; exact hdiag i _
  · have he : j = !i := by cases i <;> cases j <;> simp_all
    subst j
    exact hoff i _

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem matrix_bridge_generators :
    Algebra.adjoin ℂ (Set.range φ ∪ Set.range ψ) =
      Algebra.adjoin ℂ (Set.range φ ∪ Set.range (bridgeLetter ψ)) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x (⟨a,rfl⟩ | ⟨a,rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨a,rfl⟩)
    · exact matrixAux_mem_adjoin φ ψ δ hd a
  · apply Algebra.adjoin_le
    rintro x (⟨a,rfl⟩ | ⟨i,rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨a,rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨matrixSingle i (!i) 1,rfl⟩)

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

attribute [local instance] OAI.NaimarkZFC.PeakingPairData.modelPartialOrder
attribute [local instance] OAI.NaimarkZFC.PeakingPairData.modelStarOrderedRing
theorem model_factors_dense :
    Dense (Algebra.adjoin ℂ (Set.range B.embedBase ∪ Set.range B.embedAux) : Set B.Model) := by
  let S : Subalgebra ℂ B.Model := Algebra.adjoin ℂ (Set.range B.embedBase ∪ Set.range B.embedAux)
  have hlift (a : B.Operators) (ha : a ∈ atomicAlgebra B.atoms) :
      (⟨a,subset_closure ha⟩ : B.Model) ∈ S := by
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases Set.mem_iUnion.mp ha with ⟨i,hi⟩
      rcases hi with ⟨b,rfl⟩
      apply Algebra.subset_adjoin
      cases i with
      | false => exact Or.inl ⟨b,rfl⟩
      | true => exact Or.inr ⟨b,rfl⟩
    | algebraMap c => exact S.algebraMap_mem c
    | add a b _ _ ha hb => exact S.add_mem ha hb
    | mul a b _ _ ha hb => exact S.mul_mem ha hb
  have hd : DenseRange (fun a : atomicAlgebra B.atoms =>
      (⟨a.1,subset_closure a.2⟩ : B.Model)) :=
    (denseRange_inclusion_iff subset_closure).mpr Set.Subset.rfl
  exact hd.mono (by rintro a ⟨a,rfl⟩; exact hlift a.1 a.2)

theorem model_words_dense :
    Dense (bridgeWordSpan B.embedBase B.modelLetter (fun a => B.expectation a = 0) : Set B.Model) := by
  have hd := B.model_factors_dense
  rw [matrix_bridge_generators B.embedBase B.embedAux B.diagonal B.model_diagonal_agree] at hd
  exact hd.mono (matrix_bridge_adjoin_le_span B.embedBase B.embedAux B.diagonal
    B.model_diagonal_agree B.expectation B.expectation_fixes)

theorem coe_core (w : BridgeCore (CStarMatrix Bool Bool A)) :
    (↑(w.eval B.embedBase B.modelLetter : B.Model) : B.Operators) = w.eval B.base B.letter := by
  induction w with
  | single i => rfl
  | double i a j => rfl
  | flank i a w c j ih =>
    change B.letter i*B.base a*(↑(w.eval B.embedBase B.modelLetter : B.Model) : B.Operators)*B.base c*B.letter j = _
    rw [ih]
    rfl

end PeakingPairData

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
section
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n]

theorem matrixState_isPureState (f : A →L[ℂ] ℂ) (hf : IsPureState f) (i : n) :
    IsPureState (matrixState f i) := by
  rw [IsPureState, mem_extremePoints]
  refine ⟨matrixState_isState f hf.1 i, ?_⟩
  intro g hg h hh hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  have hface := state_projection_face g h hg hh (matrixSingle i i (1:A))
    (matrixSingle_projection i 1 (by constructor <;> simp [IsIdempotentElem,IsSelfAdjoint]))
    a b ha hb hab (by rw [heq]; simp [((isState_iff f).mp hf.1).1])
  have hgc := matrix_corner_isState g hg i hface.1
  have hhc := matrix_corner_isState h hh i hface.2
  have heqc : a • (g.comp (matrixSingleCLM i)) + b • (h.comp (matrixSingleCLM i)) = f := by
    ext x
    have he := congrArg (fun k : CStarMatrix n n A →L[ℂ] ℂ => k (matrixSingle i i x)) heq
    change a • g (matrixSingle i i x) + b • h (matrixSingle i i x) = f x
    simpa using he
  have hbase := (mem_extremePoints.mp hf).2 _ hgc _ hhc ⟨a,b,ha,hb,hab,heqc⟩
  constructor
  · ext M
    rw [matrix_state_supported g hg i hface.1 M,matrixState_apply]
    exact congrArg (fun k : A →L[ℂ] ℂ => k (M i i)) hbase.1
  · ext M
    rw [matrix_state_supported h hh i hface.2 M,matrixState_apply]
    exact congrArg (fun k : A →L[ℂ] ℂ => k (M i i)) hbase.2

omit [PartialOrder A] [StarOrderedRing A] in

theorem matrix_conjugate_entry (M : CStarMatrix n n A) (i j : n) (a : A) :
    (star M * matrixSingle j j a * M) i i = star (M j i)*a*M j i := by
  change ((CStarMatrix.ofMatrix.symm M).conjTranspose * Matrix.single j j a *
    CStarMatrix.ofMatrix.symm M) i i = _
  simp [Matrix.mul_apply,Matrix.single,Matrix.conjTranspose_apply,ite_and]

theorem matrix_pure_equivalence_reflects (f g : A →L[ℂ] ℂ)
    (hf : IsPureState f) (hg : IsPureState g) (i j : n)
    (he : UnitarilyEquivalent
      (pureGNS (matrixState f i) (matrixState_isPureState f hf i))
      (pureGNS (matrixState g j) (matrixState_isPureState g hg j))) :
    UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg) := by
  let F := positiveOfSquares (matrixState f i) (matrixState_isState f hf.1 i).2
  let G := positiveOfSquares (matrixState g j) (matrixState_isState g hg.1 j).2
  have hFn : ‖gnsVector F‖ = 1 := gnsVector_norm_eq_one F
    ((isState_iff _).mp (matrixState_isState f hf.1 i)).1
  have hGn : ‖gnsVector G‖ = 1 := gnsVector_norm_eq_one G
    ((isState_iff _).mp (matrixState_isState g hg.1 j)).1
  obtain ⟨u,hu⟩ := equivalent_vector_states_unitary F.gnsNonUnitalStarAlgHom
    (pure_gns_irreducible _ (matrixState_isState f hf.1 i) (matrixState_isPureState f hf i))
    G.gnsNonUnitalStarAlgHom he (gnsVector F) (gnsVector G) hFn hGn
  have hFc (a : CStarMatrix n n A) :
      ⟪gnsVector F,F.gnsNonUnitalStarAlgHom a (gnsVector F)⟫_ℂ = matrixState f i a :=
    gnsVector_coefficient F a
  have hGc (a : CStarMatrix n n A) :
      ⟪gnsVector G,G.gnsNonUnitalStarAlgHom a (gnsVector G)⟫_ℂ = matrixState g j a :=
    gnsVector_coefficient G a
  have hc (a : A) : g a = f (star ((u : CStarMatrix n n A) j i)*a*(u : CStarMatrix n n A) j i) := by
    have hh := hu (matrixSingle j j a)
    simpa only [hFc,hGc,matrixState_apply,
      matrixSingle_apply,ite_true, if_true,and_self,matrix_conjugate_entry] using hh
  let f₀ := positiveOfSquares f hf.1.2
  let g₀ := positiveOfSquares g hg.1.2
  let π := f₀.gnsNonUnitalStarAlgHom
  let ρ := g₀.gnsNonUnitalStarAlgHom
  let ξ := gnsVector f₀
  let η := gnsVector g₀
  let v : A := (u : CStarMatrix n n A) j i
  have hcoeff (a : A) : ⟪π v ξ,π a (π v ξ)⟫_ℂ = ⟪η,ρ a η⟫_ℂ := by
    calc
      _ = f (star v*a*v) := by
        have he : ⟪ξ,π (star v*a*v) ξ⟫_ℂ = f (star v*a*v) :=
          gnsVector_coefficient f₀ _
        rw [map_mul,map_mul,map_star,mul_apply_eq_comp,mul_apply_eq_comp,
          ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at he
        exact he
      _ = _ := (hc a).symm.trans (gnsVector_coefficient g₀ a).symm
  have hη : η ≠ 0 := by
    have hn := gnsVector_norm_eq_one g₀ ((isState_iff g).mp hg.1).1
    exact norm_ne_zero_iff.mp (hn.trans_ne one_ne_zero)
  have hξ : π v ξ ≠ 0 := by
    intro hz
    have hh := hcoeff 1
    rw [hz,inner_zero_left] at hh
    exact zero_ne_one ((hh.trans (gnsVector_coefficient g₀ 1)).trans ((isState_iff g).mp hg.1).1)
  exact irreducible_equivalent_of_coefficients π (pure_gns_irreducible f hf.1 hf)
    ρ (pure_gns_irreducible g hg.1 hg) (π v ξ) η hξ hη hcoeff

end

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {ι κ : Type*} [Preorder ι] [Preorder κ]
  [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]

theorem state_cross_excision (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (x : ι → A) (y : κ → A)
    (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1)
    (hy : ∀ j, 0 ≤ y j) (hyn : ∀ j, ‖y j‖ ≤ 1) (hym : Antitone y)
    (hexc : ∀ a, Tendsto (fun i => x i*(a-f a • (1:A))*x i) atTop (𝓝 0))
    (hey : ∀ a, Tendsto (fun j => y j*(a-g a • (1:A))*y j) atTop (𝓝 0))
    (hne : ¬ UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg)) (a : A) :
    Tendsto (fun ij : ι × κ => x ij.1*a*y ij.2) atTop (𝓝 0) := by
  apply cross_excision_tendsto x y f hx hxn hy hyn hym hexc a
  let F := positiveOfSquares f hf.1.2
  let G := positiveOfSquares g hg.1.2
  have hfcoef (b : A) : ⟪gnsVector F,F.gnsNonUnitalStarAlgHom b (gnsVector F)⟫_ℂ = f b :=
    gnsVector_coefficient F b
  have hgcoef (b : A) : ⟪gnsVector G,G.gnsNonUnitalStarAlgHom b (gnsVector G)⟫_ℂ = g b :=
    gnsVector_coefficient G b
  have ht := excision_inequivalent_strong G.gnsNonUnitalStarAlgHom
    (pure_gns_irreducible g hg.1 hg) (gnsVector G)
    (gnsVector_norm_eq_one G ((isState_iff g).mp hg.1).1) y hy hyn
    (fun b => by simpa only [hgcoef] using hey b)
    F.gnsNonUnitalStarAlgHom (pure_gns_irreducible f hf.1 hf)
    (fun h => hne h.symm) (F.gnsNonUnitalStarAlgHom (star a) (gnsVector F))
  simpa only [star_star,hfcoef] using
    vector_sandwich_tendsto F.gnsNonUnitalStarAlgHom (gnsVector F) y (star a) ht

end

open Filter Topology
section
variable {F B γ : Type*} [CStarAlgebra F] [CStarAlgebra B] {l : Filter γ}
  (φ : F →⋆ₐ[ℂ] B) (b e : Bool → B) (P : B) (hP : IsStarProjection P)
  (hel : ∀ i, e i*b i = b i) (her : ∀ i, b i*e (!i) = b i)
  (hen : ∀ i, ‖e i‖ ≤ 1) (K : F → Prop)
  (hz : ∀ w : BridgeCore F, w.Centered K → (1-P)*w.eval φ b*(1-P) = 0)
include hel her hen hz hP

theorem supported_core_decay (w : BridgeCore F) (hw : w.Centered K)
    (x y : γ → B) (hx : ∀ k, ‖x k‖ ≤ 1) (hy : ∀ k, ‖y k‖ ≤ 1) (a c : F)
    (hl : Tendsto (fun k => x k*φ a*e w.left*P) l (𝓝 0))
    (hr : Tendsto (fun k => P*(e w.right*φ c*y k)) l (𝓝 0)) :
    Tendsto (fun k => x k*φ a*w.eval φ b*φ c*y k) l (𝓝 0) := by
  have hd (k : γ) : ‖x k*φ a*e w.left‖ ≤ ‖φ a‖ := by
    calc
      _ ≤ ‖x k‖*‖φ a‖*‖e w.left‖ := norm_mul₃_le
      _ ≤ 1*‖φ a‖*1 := by gcongr <;> first | exact hx k | exact hen _
      _ = _ := by rw [one_mul,mul_one]
  have he (k : γ) : ‖e w.right*φ c*y k‖ ≤ ‖φ c‖ := by
    calc
      _ ≤ ‖e w.right‖*‖φ c‖*‖y k‖ := norm_mul₃_le
      _ ≤ 1*‖φ c‖*1 := by gcongr <;> first | exact hy k | exact hen _
      _ = _ := by rw [one_mul,mul_one]
  have ht := two_end_tendsto P (w.eval φ b) hP (hz w hw)
    (fun k => x k*φ a*e w.left) (fun k => e w.right*φ c*y k)
    ‖φ a‖ ‖φ c‖ hd he hl hr
  have hid (k : γ) : (x k*φ a*e w.left)*w.eval φ b*(e w.right*φ c*y k) =
      x k*φ a*w.eval φ b*φ c*y k := by
    calc
      _ = x k*φ a*(e w.left*w.eval φ b*e w.right)*φ c*y k := by simp only [mul_assoc]
      _ = _ := by rw [w.left_support φ b e hel,w.right_support φ b e her]
  simpa only [hid] using ht

omit hel her hen hz hP

theorem bridge_split (f : Bool → F →L[ℂ] ℂ) (tag : Option Bool) (i : Bool) (a : F) :
    a = bridgeZeroPart f tag i a + bridgeScalarPart f tag i a • 1 := by
  by_cases h : tag = some i <;> simp [bridgeZeroPart,bridgeScalarPart,h]

theorem bridgeZeroPart_good (f : Bool → F →L[ℂ] ℂ) (hf : ∀ i, f i 1 = 1)
    (tag : Option Bool) (i : Bool) (a : F) :
    tag ≠ some i ∨ f i (bridgeZeroPart f tag i a) = 0 := by
  by_cases h : tag = some i
  · right
    simp [bridgeZeroPart,h,map_sub,map_smul,hf]
  · exact Or.inl h

variable {f : Bool → F →L[ℂ] ℂ} {x y : γ → B} {px py : Bool → γ → B} {tx ty : Option Bool}
  (D : BridgeDecayData φ b e P K (l := l) f x y px py tx ty)
include hel her hen hz hP D

theorem bridge_left_transfer (i : Bool) (hi : tx = some i)
    (w : BridgeCore F) (hw : w.Centered K) (a c : F) (ha : K a)
    (hc : ty ≠ some w.right ∨ f w.right c = 0) :
    Tendsto (fun k => x k*b i*φ a*w.eval φ b*φ c*y k) l (𝓝 0) := by
  have ht := supported_core_decay φ b e P hP hel her hen K hz w hw
    (px (!i)) y (D.normPX _) D.normY a c (D.cutPX _ _ _ ha) (D.cutY _ _ hc)
  have he (k : γ) : x k*b i*φ a*w.eval φ b*φ c*y k =
      b i*(px (!i) k*φ a*w.eval φ b*φ c*y k) := by
    rw [D.matchedX i hi k,D.transferX]
    simp only [mul_assoc]
  simpa only [he,mul_zero] using tendsto_const_nhds.mul ht

theorem bridge_right_transfer (j : Bool) (hj : ty = some (!j))
    (w : BridgeCore F) (hw : w.Centered K) (a c : F) (hc : K c)
    (ha : tx ≠ some w.left ∨ f w.left a = 0) :
    Tendsto (fun k => x k*φ a*w.eval φ b*φ c*b j*y k) l (𝓝 0) := by
  have ht := supported_core_decay φ b e P hP hel her hen K hz w hw
    x (py j) D.normX (D.normPY _) a c (D.cutX _ _ ha) (D.cutPY _ _ _ hc)
  have he (k : γ) : x k*φ a*w.eval φ b*φ c*b j*y k =
      (x k*φ a*w.eval φ b*φ c*py j k)*b j := by
    rw [D.matchedY (!j) hj k]
    simp only [mul_assoc,D.transferY]
  simpa only [he,zero_mul] using ht.mul tendsto_const_nhds

theorem bridge_left_term (w : BridgeCore F) (hw : w.Centered K)
    (hi : tx = some w.left) (c : F)
    (hc : ty ≠ some w.right ∨ f w.right c = 0) :
    Tendsto (fun k => x k*w.eval φ b*φ c*y k) l (𝓝 0) := by
  cases w with
  | single i =>
    have ht := D.crossX i c hi (D.exclude i hi)
    have he (k : γ) : x k*b i*φ c*y k = b i*(px (!i) k*φ c*y k) := by
      rw [D.matchedX i hi k,D.transferX]
      simp only [mul_assoc]
    simpa only [BridgeCore.eval,he,mul_zero] using
      (tendsto_const_nhds (x := b i)).mul ht
  | double i a j =>
    simpa only [BridgeCore.eval,mul_assoc] using
      bridge_left_transfer φ b e P hP hel her hen K hz D i hi (.single j) trivial a c hw hc
  | flank i a w d j =>
    have ht := bridge_left_transfer φ b e P hP hel her hen K hz D i hi
      (w.snoc d j) (w.centered_snoc K d j hw.2.2 hw.2.1) a c hw.1
      (by rw [BridgeCore.right_snoc]; exact hc)
    simpa only [BridgeCore.eval_snoc,BridgeCore.eval,mul_assoc] using ht

theorem bridge_right_term (w : BridgeCore F) (hw : w.Centered K)
    (hj : ty = some w.right) (a : F)
    (ha : tx ≠ some w.left ∨ f w.left a = 0) :
    Tendsto (fun k => x k*φ a*w.eval φ b*y k) l (𝓝 0) := by
  cases w with
  | single i =>
    have hne : tx ≠ some i := fun hi => D.exclude i hi hj
    have ht := D.crossY i a hj hne
    have he (k : γ) : x k*φ a*b i*y k = (x k*φ a*py i k)*b i := by
      rw [D.matchedY (!i) hj k]
      simp only [mul_assoc,D.transferY]
    simpa only [BridgeCore.eval,he,zero_mul] using
      ht.mul (tendsto_const_nhds (x := b i))
  | double i c j =>
    simpa only [BridgeCore.eval,mul_assoc] using
      bridge_right_transfer φ b e P hP hel her hen K hz D j hj (.single i) trivial a c hw ha
  | flank i c w d j =>
    have ht := bridge_right_transfer φ b e P hP hel her hen K hz D j hj
      (w.cons i c) (w.centered_cons K i c hw.1 hw.2.1) a d hw.2.2
      (by rw [BridgeCore.left_cons]; exact ha)
    simpa only [BridgeCore.eval_cons,BridgeCore.eval,mul_assoc] using ht

theorem bridge_both_term (w : BridgeCore F) (hw : w.Centered K)
    (hi : tx = some w.left) (hj : ty = some w.right) :
    Tendsto (fun k => x k*w.eval φ b*y k) l (𝓝 0) := by
  cases w with
  | single i => exact (D.exclude i hi hj).elim
  | double i a j =>
    have hne : (!j) ≠ (!i) := by
      intro h
      exact D.exclude i hi (hj.trans (congrArg some h))
    have heq : j = !i := by cases i <;> cases j <;> simp_all
    have ht := D.rectangle (!i) a hw
    have he (k : γ) : x k*(b i*φ a*b j)*y k =
        b i*(px (!i) k*φ a*py (!i) k)*b j := by
      rw [D.matchedX i hi k,D.matchedY (!j) hj k]
      calc
        _ = (px i k*b i)*φ a*(b j*py (!j) k) := by simp only [mul_assoc]
        _ = _ := by rw [D.transferX,D.transferY,heq]; simp only [mul_assoc]
    simpa only [BridgeCore.eval,he,mul_zero,zero_mul] using
      ((tendsto_const_nhds (x := b i)).mul ht).mul (tendsto_const_nhds (x := b j))
  | flank i a w c j =>
    have ht := supported_core_decay φ b e P hP hel her hen K hz w hw.2.1
      (px (!i)) (py j) (D.normPX _) (D.normPY _) a c
      (D.cutPX _ _ _ hw.1) (D.cutPY _ _ _ hw.2.2)
    have he (k : γ) : x k*(b i*φ a*w.eval φ b*φ c*b j)*y k =
        b i*(px (!i) k*φ a*w.eval φ b*φ c*py j k)*b j := by
      rw [D.matchedX i hi k,D.matchedY (!j) hj k]
      calc
        _ = (px i k*b i)*φ a*w.eval φ b*φ c*(b j*py (!j) k) := by simp only [mul_assoc]
        _ = _ := by rw [D.transferX,D.transferY]; simp only [mul_assoc]
    simpa only [BridgeCore.eval,he,mul_zero,zero_mul] using
      ((tendsto_const_nhds (x := b i)).mul ht).mul (tendsto_const_nhds (x := b j))

theorem bridge_word_decay (w : BridgeCore F) (hw : w.Centered K) (a c : F) :
    Tendsto (fun k => x k*φ a*w.eval φ b*φ c*y k) l (𝓝 0) := by
  let a' := bridgeZeroPart f tx w.left a
  let c' := bridgeZeroPart f ty w.right c
  let α := bridgeScalarPart f tx w.left a
  let β := bridgeScalarPart f ty w.right c
  have ha : tx ≠ some w.left ∨ f w.left a' = 0 := bridgeZeroPart_good f D.normState tx w.left a
  have hc : ty ≠ some w.right ∨ f w.right c' = 0 := bridgeZeroPart_good f D.normState ty w.right c
  have h00 := supported_core_decay φ b e P hP hel her hen K hz w hw
    x y D.normX D.normY a' c' (D.cutX _ _ ha) (D.cutY _ _ hc)
  have h10 : Tendsto (fun k => α • (x k*w.eval φ b*φ c'*y k)) l (𝓝 0) := by
    by_cases hi : tx = some w.left
    · simpa only [smul_zero] using
        (bridge_left_term φ b e P hP hel her hen K hz D w hw hi c' hc).const_smul α
    · simp only [α,bridgeScalarPart,ite_eq_right hi,zero_smul]
      exact tendsto_const_nhds
  have h01 : Tendsto (fun k => β • (x k*φ a'*w.eval φ b*y k)) l (𝓝 0) := by
    by_cases hj : ty = some w.right
    · simpa only [smul_zero] using
        (bridge_right_term φ b e P hP hel her hen K hz D w hw hj a' ha).const_smul β
    · simp only [β,bridgeScalarPart,ite_eq_right hj,zero_smul]
      exact tendsto_const_nhds
  have h11 : Tendsto (fun k => (α*β) • (x k*w.eval φ b*y k)) l (𝓝 0) := by
    by_cases hi : tx = some w.left
    · by_cases hj : ty = some w.right
      · simpa only [smul_zero] using
          (bridge_both_term φ b e P hP hel her hen K hz D w hw hi hj).const_smul (α*β)
      · simp only [β,bridgeScalarPart,ite_eq_right hj,mul_zero,zero_smul]
        exact tendsto_const_nhds
    · simp only [α,bridgeScalarPart,ite_eq_right hi,zero_mul,zero_smul]
      exact tendsto_const_nhds
  have ht := (h00.add h10).add (h01.add h11)
  have he (k : γ) := bridge_four_terms φ a c a' c' α β
    (bridge_split f tx w.left a) (bridge_split f ty w.right c) (x k) (y k) (w.eval φ b)
  simpa only [← he,add_zero] using ht

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule
section
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in

theorem unique_extension_of_dense_word_decay {ι : Type*} {l : Filter ι} [l.NeBot]
    (φ : A →⋆ₐ[ℂ] B) (h : A →L[ℂ] ℂ) (W : Set B)
    (hdense : Dense (Submodule.span ℂ (Set.range φ ∪ W) : Set B))
    (x : ι → A) (hx : ∀ i, ‖x i‖ ≤ 1) (hself : ∀ i, IsSelfAdjoint (x i))
    (hxval : ∀ i, h (x i) = 1)
    (hdecay : ∀ w ∈ W, Tendsto (fun i => φ (x i)*w*φ (x i)) l (𝓝 0))
    (g₁ g₂ : B →L[ℂ] ℂ) (hg₁ : IsState g₁) (hg₂ : IsState g₂)
    (hres₁ : restrictState φ g₁ = h) (hres₂ : restrictState φ g₂ = h) : g₁ = g₂ := by
  have hzero (g : B →L[ℂ] ℂ) (hg : IsState g) (hres : restrictState φ g = h)
      (w : B) (hw : w ∈ W) : g w = 0 := by
    have hc (i : ι) : g (φ (x i)*w*φ (x i)) = g w :=
      state_compression g hg (φ (x i))
        ((NonUnitalStarAlgHom.norm_apply_le φ _).trans (hx i))
        ((hself i).map φ) (by
          change restrictState φ g (x i) = 1
          rw [hres,hxval]) w
    have ht := g.continuous.tendsto 0 |>.comp (hdecay w hw)
    have ht' : Tendsto (fun _ : ι => g w) l (𝓝 (0 : ℂ)) := by
      simpa only [Function.comp_def,hc,map_zero] using ht
    exact tendsto_nhds_unique tendsto_const_nhds ht'
  apply ContinuousLinearMap.ext_on hdense
  intro b hb
  rcases hb with ⟨a,rfl⟩ | hw
  · change restrictState φ g₁ a = restrictState φ g₂ a
    rw [hres₁,hres₂]
  · rw [hzero g₁ hg₁ hres₁ b hw,hzero g₂ hg₂ hres₂ b hw]

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
section

variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

variable [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in

theorem simple_matrix_corner_injective (hA : IsSimpleCStar A)
    (π : CStarMatrix Bool Bool A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (i : Bool)
    (hne : π (matrixSingle i i (1 : A)) ≠ 0) :
    Function.Injective (π.comp (matrixSingleHom i)) := by
  apply simple_nonzeroStarHom_injective hA
  intro he
  apply hne
  exact congrArg (fun φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H) => φ 1) he

theorem matrix_pure_corner_ne_zero (f : A →L[ℂ] ℂ) (hf : IsPureState f) (i : Bool) :
    pureGNS (matrixState f i) (matrixState_isPureState f hf i)
      (matrixSingle i i (1 : A)) ≠ 0 := by
  let F := positiveOfSquares (matrixState f i) (matrixState_isState f hf.1 i).2
  intro hz
  have hc := gnsVector_coefficient F (matrixSingle i i (1:A))
  change ⟪gnsVector F,
    pureGNS (matrixState f i) (matrixState_isPureState f hf i)
      (matrixSingle i i (1:A)) (gnsVector F)⟫_ℂ = matrixState f i (matrixSingle i i 1) at hc
  rw [hz,zero_apply,inner_zero_right] at hc
  simp only [matrixState_apply,matrixSingle_apply,ite_true, if_true,true_and] at hc
  exact zero_ne_one (hc.trans ((isState_iff f).mp hf.1).1)

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev pureIndex (_B : PeakingPairData A) (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f) :=
  ExcisionIndex (vectorNullAlgebra (pureGNS f hf)
    (gnsVector (positiveOfSquares f hf.1.2))) × ℕ

instance pureIndexDirected (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f) :
    IsDirectedOrder (B.pureIndex f hf) := ⟨by
  intro x y
  obtain ⟨z,hxz,hyz⟩ := exists_ge_ge x.1 y.1
  exact ⟨(z,max x.2 y.2),⟨hxz,le_max_left _ _⟩,⟨hyz,le_max_right _ _⟩⟩⟩

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
theorem matrixSingle_representation_ne_zero
    {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]
    (π : CStarMatrix Bool Bool A →⋆ₙₐ[ℂ] C) (i : Bool)
    (hinj : Function.Injective (π.comp (matrixSingleHom i))) {a : A} (ha : a ≠ 0) :
    π (matrixSingle i i a) ≠ 0 := by
  intro hz
  apply ha
  apply hinj
  change π (matrixSingle i i a) = π (matrixSingle i i (0:A))
  rw [hz,matrixSingle_zero,map_zero]

open scoped CStarAlgebra ComplexOrder InnerProductSpace
section
universe u v
variable {A : Type u} {C : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

def StateExtensionUnique (φ : A →⋆ₐ[ℂ] C) (f : A →L[ℂ] ℂ) : Prop :=
  ∀ g₁ g₂ : C →L[ℂ] ℂ, IsState g₁ → IsState g₂ →
    restrictState φ g₁ = f → restrictState φ g₂ = f → g₁ = g₂

omit [PartialOrder A] [StarOrderedRing A] in

theorem StateExtensionUnique.transport {φ : A →⋆ₐ[ℂ] C} {f : A →L[ℂ] ℂ}
    (hu : StateExtensionUnique φ f) (α : A ≃⋆ₐ[ℂ] A) (β : C ≃⋆ₐ[ℂ] C)
    (hc : ∀ a, φ (α a) = β (φ a)) :
    StateExtensionUnique φ (restrictState α.toStarAlgHom f) := by
  have hs (a : A) : φ (α.symm a) = β.symm (φ a) := by
    apply β.injective
    change β (φ (α.symm a)) = β (β.symm (φ a))
    rw [β.apply_symm_apply,← hc,α.apply_symm_apply]
  intro g₁ g₂ hg₁ hg₂ hr₁ hr₂
  have hres (g : C →L[ℂ] ℂ) (hr : restrictState φ g = restrictState α.toStarAlgHom f) :
      restrictState φ (restrictState β.symm.toStarAlgHom g) = f := by
    ext a
    change g (β.symm (φ a)) = f a
    rw [← hs]
    change restrictState φ g (α.symm a) = f a
    rw [hr]
    change f (α (α.symm a)) = f a
    rw [α.apply_symm_apply]
  have he := hu _ _ (isState_restrict _ _ hg₁) (isState_restrict _ _ hg₂)
    (hres g₁ hr₁) (hres g₂ hr₂)
  ext c
  have hh := congrArg (fun g : C →L[ℂ] ℂ => g (β c)) he
  change g₁ (β.symm (β c)) = g₂ (β.symm (β c)) at hh
  simpa only [β.symm_apply_apply] using hh

theorem pureState_equivalent_conjugate (f h : A →L[ℂ] ℂ)
    (hf : IsPureState f) (hh : IsPureState h)
    (he : UnitarilyEquivalent (pureGNS f hf) (pureGNS h hh)) :
    ∃ u : unitary A, h = restrictState (Unitary.conjStarAlgAut ℂ A u).symm.toStarAlgHom f := by
  let F := positiveOfSquares f hf.1.2
  let G := positiveOfSquares h hh.1.2
  obtain ⟨u,hu⟩ := equivalent_vector_states_unitary (pureGNS f hf)
    (pure_gns_irreducible f hf.1 hf) (pureGNS h hh) he (gnsVector F) (gnsVector G)
    (gnsVector_norm_eq_one F ((isState_iff f).mp hf.1).1)
    (gnsVector_norm_eq_one G ((isState_iff h).mp hh.1).1)
  refine ⟨u, ?_⟩
  ext a
  have hF (a : A) : ⟪gnsVector F, pureGNS f hf a (gnsVector F)⟫_ℂ = f a :=
    gnsVector_coefficient F a
  have hG (a : A) : ⟪gnsVector G, pureGNS h hh a (gnsVector G)⟫_ℂ = h a :=
    gnsVector_coefficient G a
  change h a = f (star (u:A)*a*(u:A))
  simpa only [hF,hG] using hu a

theorem StateExtensionUnique.of_equivalent {φ : A →⋆ₐ[ℂ] C}
    {f h : A →L[ℂ] ℂ} (hu : StateExtensionUnique φ f)
    (hf : IsPureState f) (hh : IsPureState h)
    (he : UnitarilyEquivalent (pureGNS f hf) (pureGNS h hh)) :
    StateExtensionUnique φ h := by
  obtain ⟨u,rfl⟩ := pureState_equivalent_conjugate f h hf hh he
  let v : unitary C := ⟨φ (u : A), by
    constructor
    · rw [← map_star,← map_mul,u.property.1,map_one]
    · rw [← map_star,← map_mul,u.property.2,map_one]⟩
  apply hu.transport (Unitary.conjStarAlgAut ℂ A u).symm
    (Unitary.conjStarAlgAut ℂ C v).symm
  intro a
  change φ (star (u:A)*a*(u:A)) = star (φ (u:A))*φ a*φ (u:A)
  simp only [map_mul,map_star]

omit [PartialOrder A] [StarOrderedRing A] in

theorem pure_extensions_inequivalent_of_no_common
    (φ : A →⋆ₐ[ℂ] C) (f h : A →L[ℂ] ℂ)
    (hno : ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      ∀ (π : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)), IsIrreducible π →
      ∀ ξ η : H, ‖ξ‖ = 1 → ‖η‖ = 1 →
      (∀ a, ⟪ξ,π (φ a) ξ⟫_ℂ = f a) →
      (∀ a, ⟪η,π (φ a) η⟫_ℂ = h a) → False)
    (g₁ g₂ : C →L[ℂ] ℂ) (hg₁ : IsPureState g₁) (hg₂ : IsPureState g₂)
    (hr₁ : restrictState φ g₁ = f) (hr₂ : restrictState φ g₂ = h) :
    ¬ UnitarilyEquivalent (pureGNS g₁ hg₁) (pureGNS g₂ hg₂) := by
  rintro ⟨U,hU⟩
  let F := positiveOfSquares g₁ hg₁.1.2
  let G := positiveOfSquares g₂ hg₂.1.2
  have hF := gnsVector_norm_eq_one F ((isState_iff g₁).mp hg₁.1).1
  have hG := gnsVector_norm_eq_one G ((isState_iff g₂).mp hg₂.1).1
  apply hno G.GNS (pureGNS g₂ hg₂) (pure_gns_irreducible g₂ hg₂.1 hg₂)
    (U (gnsVector F)) (gnsVector G) (by rw [U.norm_map,hF]) hG
  · intro a
    rw [← hU (φ a) (gnsVector F),U.inner_map_map]
    change ⟪gnsVector F,F.gnsStarAlgHom (φ a) (gnsVector F)⟫_ℂ = f a
    rw [gnsVector_coefficient]
    exact congrArg (fun k : A →L[ℂ] ℂ => k a) hr₁
  · intro a
    change ⟪gnsVector G,G.gnsStarAlgHom (φ a) (gnsVector G)⟫_ℂ = h a
    rw [gnsVector_coefficient]
    exact congrArg (fun k : A →L[ℂ] ℂ => k a) hr₂

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A]

theorem isState_of_unital_contractive_hermitian (f : A →L[ℂ] ℂ)
    (h1 : f 1 = 1) (hn : ∀ a, ‖f a‖ ≤ ‖a‖)
    (hstar : ∀ a, f (star a) = star (f a)) : IsState f := by
  let sa : selfAdjoint A →L[ℝ] A :=
    ((selfAdjoint.submodule ℝ A).subtype).mkContinuous 1 (fun a => by simp)
  let g : selfAdjoint A →L[ℝ] ℝ := Complex.reCLM.comp ((f.restrictScalars ℝ).comp sa)
  have hg : ‖g‖ ≤ 1 := by
    apply g.opNorm_le_bound zero_le_one
    intro a
    change ‖(f (a:A)).re‖ ≤ 1*‖a‖
    rw [one_mul,Real.norm_eq_abs]
    change |(f (a:A)).re| ≤ ‖(a:A)‖
    exact (Complex.abs_re_le_norm _).trans (hn a)
  apply (isState_iff f).mpr
  refine ⟨h1,fun a => ?_⟩
  have hsa : IsSelfAdjoint (star a*a) := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg a)
  have hi : (f (star a*a)).im = 0 := by
    have hh := hstar (star a*a)
    rw [hsa.star_eq] at hh
    exact Complex.conj_eq_iff_im.mp hh.symm
  refine ⟨hi,?_⟩
  exact selfAdjoint_nonneg_of_norm_one g hg (by change (f 1).re = 1; rw [h1]; rfl)
    ⟨star a*a,hsa⟩ (star_mul_self_nonneg a)

variable (e : A) (he : IsStarProjection e)

theorem cornerLiftState_isState (g : CStarCorner e he →L[ℂ] ℂ) (hg : IsState g) :
    IsState (cornerLiftState e he g) := by
  apply isState_of_unital_contractive_hermitian
  · change g (cornerCompression e he (1:A)) = 1
    have h : cornerCompression e he (1:A) = 1 := by
      apply Subtype.ext
      change e*1*e=e
      rw [mul_one,he.isIdempotentElem.eq]
    rw [h,((isState_iff g).mp hg).1]
  · intro a
    exact (state_norm_apply_le g hg _).trans (cornerCompression_norm e he a)
  · intro a
    have h : cornerCompression e he (star a) = star (cornerCompression e he a) := by
      apply Subtype.ext
      change e*star a*e=star (e*a*e)
      simp only [star_mul,he.isSelfAdjoint.star_eq,mul_assoc]
    change g (cornerCompression e he (star a)) = star (g (cornerCompression e he a))
    rw [h,state_map_star g hg]

variable [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder C] [StarOrderedRing C] in

theorem matrixCorner_compression (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
    (M : CStarMatrix Bool Bool A) :
    cornerCompression (matrixCornerProjection φ) (matrixCornerProjection_isProjection φ) (φ M) =
      matrixCornerBase φ (M false false) := by
  apply Subtype.ext
  change φ (matrixSingle false false (1:A))*φ M*φ (matrixSingle false false (1:A)) =
    φ (matrixSingle false false (M false false))
  rw [← map_mul,← map_mul,matrixSingle_compress,one_mul,mul_one]

theorem corner_unique_of_matrix (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
    (f : A →L[ℂ] ℂ) (hu : StateExtensionUnique φ (matrixState f false)) :
    StateExtensionUnique (matrixCornerBase φ) f := by
  intro g₁ g₂ hg₁ hg₂ hr₁ hr₂
  let e := matrixCornerProjection φ
  let he := matrixCornerProjection_isProjection φ
  have hres (g : MatrixHNNCorner φ →L[ℂ] ℂ) (hr : restrictState (matrixCornerBase φ) g = f) :
      restrictState φ (cornerLiftState e he g) = matrixState f false := by
    ext M
    change g (cornerCompression e he (φ M)) = f (M false false)
    rw [matrixCorner_compression]
    exact congrArg (fun k : A →L[ℂ] ℂ => k (M false false)) hr
  have hh := hu _ _ (cornerLiftState_isState e he g₁ hg₁)
    (cornerLiftState_isState e he g₂ hg₂) (hres g₁ hr₁) (hres g₂ hr₂)
  ext a
  have ha := congrArg (fun k : C →L[ℂ] ℂ => k (a:C)) hh
  simpa only [cornerLiftState_apply,cornerCompression_corner] using ha

end

section
variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

theorem exists_state_extension_of_injective (φ : A →⋆ₐ[ℂ] C)
    (hφ : Function.Injective φ) (f : A →L[ℂ] ℂ) (hf : IsState f) :
    ∃ g : C →L[ℂ] ℂ, IsState g ∧ restrictState φ g = f := by
  let : IsClosed (φ.range : Set C) :=
    (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosed_range
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder φ.range := CStarAlgebra.spectralOrder φ.range
  let : StarOrderedRing φ.range := CStarAlgebra.spectralOrderedRing φ.range
  let e := StarAlgEquiv.ofInjective φ hφ
  let h := restrictState e.symm.toStarAlgHom f
  obtain ⟨g,hg,hres⟩ := exists_state_extension_subalgebra φ.range h
    (isState_restrict _ _ hf)
  refine ⟨g,hg,?_⟩
  ext a
  have hh := hres (e a)
  change g (φ a) = f a
  change g (φ a) = f (e.symm (e a)) at hh
  simpa only [e.symm_apply_apply] using hh

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder C] [StarOrderedRing C]

theorem StateExtensionUnique.exists_unique_pure {φ : A →⋆ₐ[ℂ] C}
    (hφ : Function.Injective φ) {f : A →L[ℂ] ℂ} (hf : IsPureState f)
    (hu : StateExtensionUnique φ f) :
    ∃ g : C →L[ℂ] ℂ, IsPureState g ∧ restrictState φ g = f ∧
      ∀ h : C →L[ℂ] ℂ, IsState h → restrictState φ h = f → h = g := by
  obtain ⟨g,hg,hr⟩ := exists_state_extension_of_injective φ hφ f hf.1
  have huniq : ∀ h : C →L[ℂ] ℂ, IsState h → restrictState φ h = f → h = g :=
    fun h hh hhr => hu h g hh hg hhr hr
  exact ⟨g,unique_lift_pure φ f hf g hg hr huniq,hr,huniq⟩

end

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra Matrix

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped InnerProductSpace lp

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (e : A) (he : IsStarProjection e)

theorem pureState_equivalent_of_conjugate (f g : A →L[ℂ] ℂ)
    (hf : IsPureState f) (hg : IsPureState g) (u : unitary A)
    (hc : ∀ a, g a = f (star (u:A)*a*(u:A))) :
    UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg) := by
  let F := positiveOfSquares f hf.1.2
  let G := positiveOfSquares g hg.1.2
  let ξ := F.gnsStarAlgHom u (gnsVector F)
  have hfc (a : A) : ⟪ξ,F.gnsStarAlgHom a ξ⟫_ℂ = g a := by
    rw [hc]
    change ⟪F.gnsStarAlgHom u (gnsVector F),
      F.gnsStarAlgHom a (F.gnsStarAlgHom u (gnsVector F))⟫_ℂ = f (star (u:A)*a*(u:A))
    change _ = F (star (u:A)*a*(u:A))
    rw [← gnsVector_coefficient F]
    simp only [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  have hξ : ξ ≠ 0 := by
    intro hz
    have hh := hfc 1
    rw [hz,inner_zero_left,((isState_iff g).mp hg.1).1] at hh
    exact zero_ne_one hh
  exact irreducible_equivalent_of_coefficients (pureGNS f hf)
    (pure_gns_irreducible f hf.1 hf) (pureGNS g hg)
    (pure_gns_irreducible g hg.1 hg) ξ (gnsVector G) hξ
    (norm_ne_zero_iff.mp ((gnsVector_norm_eq_one G ((isState_iff g).mp hg.1).1).trans_ne one_ne_zero))
    (fun a => (hfc a).trans (gnsVector_coefficient G a).symm)

end

open scoped CStarAlgebra ComplexOrder

section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def PureStateEquivalent (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (g : A →L[ℂ] ℂ) (hg : IsPureState g) : Prop :=
  UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg)

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_pure_norming_state [Nontrivial A] (a : A) (ha : 0 ≤ a) :
    ∃ f : A →L[ℂ] ℂ, IsPureState f ∧ (f a).re = ‖a‖ := by
  let S : Set (WeakDual ℂ A) := {f | f ∈ weakStates A ∧ (f a).re = ‖a‖}
  have hS : IsCompact S := isCompact_weakStates.inter_right
    (isClosed_eq (Complex.continuous_re.comp (WeakDual.eval_continuous a)) continuous_const)
  have hne : S.Nonempty := by
    let : IsStarNormal a := (IsSelfAdjoint.of_nonneg ha).isStarNormal
    obtain ⟨f, hf, hnorm⟩ := exists_norming_state a
    refine ⟨StrongDual.toWeakDual f, hf, ?_⟩
    have hp := state_nonneg f hf ha
    change (f a).re = ‖a‖
    have he := Complex.norm_of_nonneg' hp
    have hre := congrArg Complex.re he
    simpa only [Complex.ofReal_re, hnorm] using hre.symm
  let : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing ℂ A)
  obtain ⟨f, hf⟩ := hS.extremePoints_nonempty hne
  rw [mem_extremePoints] at hf
  refine ⟨f.toStrongDual, ?_, hf.1.2⟩
  rw [IsPureState, mem_extremePoints]
  refine ⟨hf.1.1, ?_⟩
  intro g hg k hk hseg
  obtain ⟨r, s, hr, hs, hrs, heq⟩ := hseg
  have hga : (g a).re ≤ ‖a‖ := (Complex.re_le_norm _).trans (state_norm_apply_le g hg a)
  have hka : (k a).re ≤ ‖a‖ := (Complex.re_le_norm _).trans (state_norm_apply_le k hk a)
  have hval := congrArg (fun l : A →L[ℂ] ℂ => (l a).re) heq
  simp only [add_apply, smul_apply, Complex.add_re, Complex.smul_re, smul_eq_mul] at hval
  change r*(g a).re+s*(k a).re = (f a).re at hval
  rw [hf.1.2] at hval
  have hscale := congrArg (fun z : ℝ => z*‖a‖) hrs
  have hgeq : (g a).re = ‖a‖ := by
    apply le_antisymm hga
    by_contra hlt
    have ht := mul_pos hr (sub_pos.mpr (lt_of_not_ge hlt))
    have hn := mul_nonneg hs.le (sub_nonneg.mpr hka)
    nlinarith
  have hkeq : (k a).re = ‖a‖ := by
    apply le_antisymm hka
    by_contra hlt
    have ht := mul_pos hs (sub_pos.mpr (lt_of_not_ge hlt))
    nlinarith
  have h := hf.2 (StrongDual.toWeakDual g) ⟨hg, hgeq⟩
    (StrongDual.toWeakDual k) ⟨hk, hkeq⟩ ⟨r,s,hr,hs,hrs, ?_⟩
  · exact ⟨congrArg WeakDual.toStrongDual h.1, congrArg WeakDual.toStrongDual h.2⟩
  · apply WeakDual.toStrongDual.injective
    exact heq

theorem positive_eq_zero_of_pure_states [Nontrivial A] (a : A) (ha : 0 ≤ a)
    (hz : ∀ f : A →L[ℂ] ℂ, IsPureState f → f a = 0) : a = 0 := by
  obtain ⟨f, hf, hnorm⟩ := exists_pure_norming_state a ha
  rw [hz f hf, Complex.zero_re] at hnorm
  exact norm_eq_zero.mp hnorm.symm

end

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open UniformSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

def PureUEP (φ : A →⋆ₐ[ℂ] B) : Prop :=
  ∀ f : A →L[ℂ] ℂ, IsPureState f → StateExtensionUnique φ f

end

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra

open Topology

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

open Topology

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open UniformSpace
open scoped ComplexOrder
section
universe u v
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)] [IsometricStarSystem A f]
  (τ : ∀ i, A i →L[ℂ] ℂ) (hτ : ∀ i, IsState (τ i))
  (hcompat : ∀ i j h a, τ j (f i j h a) = τ i a)

attribute [local instance] OAI.NaimarkZFC.directLimitNormTopology
def directLimitFunctional : DirectLimit A f →L[ℂ] ℂ :=
  (DirectLimit.Module.lift ℂ I A f (fun i => (τ i).toLinearMap) hcompat).mkContinuous 1 (by
    intro a
    induction a using DirectLimit.induction f with
    | ih i a =>
      change ‖τ i a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using state_norm_apply_le (τ i) (hτ i) a)

@[simp] theorem directLimitFunctional_stage (i : I) (a : A i) :
    directLimitFunctional A f τ hτ hcompat (directLimitInclude A f i a) = τ i a := rfl

def cstarDirectLimitState : CStarDirectLimit A f →L[ℂ] ℂ :=
  (directLimitFunctional A f τ hτ hcompat).fromCompletion

@[simp] theorem cstarDirectLimitState_stage (i : I) (a : A i) :
    cstarDirectLimitState A f τ hτ hcompat (cstarDirectLimitInclude A f i a) = τ i a :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

end

open scoped CStarAlgebra ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem tracialState_strictPos_of_simple (hA : IsSimpleCStar A)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (htr : ∀ a b, τ (a*b) = τ (b*a))
    (a : A) (ha : a ≠ 0) : 0 < (τ (star a*a)).re := by
  let T := positiveOfSquares τ hτ.2
  let π := T.gnsStarAlgHom
  have hn : ‖gnsVector T‖ = 1 := gnsVector_norm_eq_one T ((isState_iff τ).mp hτ).1
  have hinj : Function.Injective π := by
    apply simple_nonzeroStarHom_injective hA π.toNonUnitalStarAlgHom
    intro hz
    have hh := congrArg (fun ψ : A →⋆ₙₐ[ℂ] (T.GNS →L[ℂ] T.GNS) =>
      ψ 1 (gnsVector T)) hz
    have he : gnsVector T = 0 := by
      change π 1 (gnsVector T) = 0 at hh
      simpa only [map_one,one_apply_eq_self] using hh
    rw [he,norm_zero] at hn
    exact zero_ne_one hn
  apply lt_of_le_of_ne (hτ.2 a).2
  intro hz
  apply ha
  apply hinj
  rw [map_zero]
  apply tracial_gns_zero_of_square_zero T htr
  apply Complex.ext
  · exact hz.symm
  · exact (hτ.2 a).1

end

open Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_CAR
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

instance carIsometricSystem : IsometricStarSystem CARStage carBond := ⟨carBond_isometry⟩

abbrev CAR := CStarDirectLimit CARStage carBond

abbrev carInclude (n : ℕ) : CARStage n →⋆ₐ[ℂ] CAR :=
  cstarDirectLimitInclude CARStage carBond n

open scoped ComplexOrder CStarAlgebra

theorem complex_identity_isState : IsState (ContinuousLinearMap.id ℂ ℂ) := by
  rw [isState_iff]
  refine ⟨rfl,fun a => ?_⟩
  have h := star_mul_self_nonneg a
  exact ⟨h.2.symm,h.1⟩

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end


