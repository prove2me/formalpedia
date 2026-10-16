-- Prove2me | Definitions.Def_MIPRE_Foundations_GameTransport
-- name    : MIPRE_Foundations_GameTransport
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:09:55.641072+00:00
-- url     : https://prove2.me/theorems/17e983ae-34e5-455e-9836-1f32c6542d1e
-- title:
--   Transport of games and strategies: relabeling, zero extension and merging of answers
-- statement:
--   Constructions transporting strategies across presentations of a game: identifying a verifier's game with its tabulation as a game description, and comparing the same game under different answer-length bounds (blueprint `rem:compression-abstract`).
--
--   **On projective measurements** (any star ring, finite outcomes). `ProjectiveMeasurement.reindex P eX eA` relabels questions along any map $e_X : X' \to X$ and answers along an equivalence $e_A : A' \simeq A$. `ProjectiveMeasurement.extend P ι`, for an embedding $\iota : A \hookrightarrow A'$, puts zero operators on the new answers. `ProjectiveMeasurement.merge P r`, for matrices over $\mathbb{C}^{n}$ and a map $r : A' \to A$, sums the outcomes with the same image:
--   $$(\mathrm{merge}\ P\ r)^{\,a}_{x} = \sum_{a' :\ r(a') = a} P^{a'}_{x} .$$
--
--   **On tensor-product strategies** for `G : Game X Y A B`: `TensorProductStrategy.copy S G'` (same data, another game), `relabel S G' eX eY eA eB`, `extendAnswers S G' ιA ιB` (zero extension along embeddings) and `mergeAnswers S' G rA rB` (merging along maps); each keeps the dimensions and the state.
--
--   **On synchronous strategies** for `G : SynchronousGame X A`: `SyncStrategy.copy S G'`, `SyncStrategy.extend S G' ι`, `SyncStrategy.relabel S G' eX eA`, and `SyncStrategy.const G a₀`, the one-dimensional strategy that always answers $a_0$.
--
--   The embedded lemmas are the `simp` rules for the operators of these constructions, the orthogonality `ProjectiveMeasurement.mul_eq_zero_of_ne` ($M^a_x M^b_x = 0$ for $a \ne b$), zero extension preserving the value (`value_extendAnswers`, `SyncStrategy.value_extend`) and the PCC property (`isPCC_extend`), `value_le_mergeAnswers` (merging can only raise the value when accepted tuples stay accepted), and `quantumValue_extendAnswers`: enlarging the answer alphabets by always-rejected answers leaves $\mathrm{val}^{*}$ unchanged.
--
--   **Formalization Note**. Question relabelings are arbitrary maps while answer relabelings are equivalences (the normalization needs it); `extend` is `noncomputable` (`Function.extend`), and `merge` is stated only over matrix algebras (it needs orthogonality of outcomes). The value lemmas take pointwise hypotheses, $\mu' = \mu$ and $D'(x,y,\iota_A a,\iota_B b) = D(x,y,a,b)$; `quantumValue_extendAnswers` also needs $G'$ to accept only pairs in the ranges of the embeddings, and $A$, $B$ nonempty with decidable equality. `quantumValue_eq_of_equiv`, `quantumValue_mono` and `syncValue_eq_of_equiv` are not in this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameTransport.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameTransport.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games

/-!
# Transport of games and strategies

Bookkeeping lemmas about the quantum value under changes of presentation of a game, used to
identify a verifier's game with its tabulation as a game description and to compare the same
game under different answer-length bounds (blueprint `rem:compression-abstract`):

* **Relabeling.** `quantumValue_eq_of_equiv`: two games related by equivalences of their four
  alphabets, with matching distribution and decision predicate, have the same quantum value.
  Strategies are transported by `TensorProductStrategy.relabel`.
* **Monotonicity.** `quantumValue_mono`: accepting more answer tuples, on the same alphabets
  and distribution, can only raise the value.
* **Answer extension.** `quantumValue_extendAnswers`: enlarging the answer alphabets by
  answers that are always rejected does not change the value. From the small game to the
  large one a strategy extends by zero operators (`ProjectiveMeasurement.extend`); from the
  large game to the small one the new answers are merged into an old one
  (`ProjectiveMeasurement.merge`), which needs the orthogonality of the outcomes of a
  projective measurement (`ProjectiveMeasurement.mul_eq_zero_of_ne`) and can only raise the
  value.
* The synchronous counterparts for PCC strategies: `SyncStrategy.relabel` plays a strategy
  through a relabeling of the questions and of the answers, keeping the value
  (`value_relabel`) and the commutation condition (`isPCC_relabel`), whence
  `syncValue_eq_of_equiv` by the same two-sided `iSup` argument as `quantumValue_eq_of_equiv`;
  `SyncStrategy.extend` keeps the value and the PCC property; and the constant strategy
  `SyncStrategy.const` is PCC with value the acceptance mass of a fixed answer pair.

The synchronous relabeling is what carries a value-`1` PCC strategy of a verifier's game to a
tabulation of it as a game description, which is item 1 of blueprint `thm:halting`; the
consumer is `MIPRE.Foundations.SyncTransport`.
-/

namespace MIPRE

open Matrix Kronecker
open scoped ComplexOrder

/-! ## Projective measurements: relabeling, zero extension, merging -/

namespace ProjectiveMeasurement

variable {X A : Type*} [Fintype A] {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜]

/-- Relabel the questions along a function and the answers along an equivalence. -/
def reindex {X' A' : Type*} [Fintype A'] (P : ProjectiveMeasurement X A 𝒜) (eX : X' → X)
    (eA : A' ≃ A) : ProjectiveMeasurement X' A' 𝒜 where
  M x' a' := P.M (eX x') (eA a')
  selfAdjoint x' a' := P.selfAdjoint _ _
  projective x' a' := P.projective _ _
  normalized x' := by rw [eA.sum_comp fun a => P.M (eX x') a]; exact P.normalized _

@[simp] theorem reindex_M {X' A' : Type*} [Fintype A'] (P : ProjectiveMeasurement X A 𝒜)
    (eX : X' → X) (eA : A' ≃ A) (x' : X') (a' : A') :
    (P.reindex eX eA).M x' a' = P.M (eX x') (eA a') := rfl

/-- Extend the answer alphabet along an embedding, with the zero operator on the new
answers. -/
noncomputable def extend {A' : Type*} [Fintype A'] (P : ProjectiveMeasurement X A 𝒜)
    (ι : A ↪ A') :
    ProjectiveMeasurement X A' 𝒜 where
  M x a' := Function.extend ι (P.M x) 0 a'
  selfAdjoint x a' := by
    by_cases h : ∃ a, ι a = a'
    · obtain ⟨a, rfl⟩ := h
      rw [ι.injective.extend_apply]
      exact P.selfAdjoint x a
    · rw [Function.extend_apply' _ _ _ h]
      simp
  projective x a' := by
    by_cases h : ∃ a, ι a = a'
    · obtain ⟨a, rfl⟩ := h
      rw [ι.injective.extend_apply]
      exact P.projective x a
    · rw [Function.extend_apply' _ _ _ h]
      simp
  normalized x := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ι)) ?_, Finset.sum_map]
    · simp only [ι.injective.extend_apply]
      exact P.normalized x
    · intro a' _ ha'
      rw [Function.extend_apply' _ _ _ fun ⟨a, ha⟩ => ha' (Finset.mem_map.2 ⟨a, Finset.mem_univ a, ha⟩)]
      rfl

@[simp] theorem extend_M_apply {A' : Type*} [Fintype A'] (P : ProjectiveMeasurement X A 𝒜)
    (ι : A ↪ A') (x : X) (a : A) : (P.extend ι).M x (ι a) = P.M x a :=
  ι.injective.extend_apply _ _ a

theorem extend_M_of_not_mem {A' : Type*} [Fintype A'] (P : ProjectiveMeasurement X A 𝒜)
    (ι : A ↪ A') (x : X) {a' : A'} (h : ¬∃ a, ι a = a') : (P.extend ι).M x a' = 0 :=
  Function.extend_apply' _ _ _ h

/-- The outcomes of a projective measurement on `ℂ^n` are mutually orthogonal:
`M x a * M x b = 0` for `a ≠ b`. -/
theorem mul_eq_zero_of_ne {n : Type*} [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) {a b : A} (hab : a ≠ b) :
    P.M x a * P.M x b = 0 := by
  classical
  -- `M a = ∑ c, M a * M c * M a`, and the term `c = a` is `M a` itself
  have hsum : ∑ c ∈ Finset.univ.erase a, P.M x a * P.M x c * P.M x a = 0 := by
    have h1 : P.M x a = ∑ c, P.M x a * P.M x c * P.M x a := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, P.normalized, mul_one, P.projective]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), P.projective, P.projective] at h1
    exact (add_eq_left.1 h1.symm)
  -- each term is `(M c * M a)ᴴ * (M c * M a)`, positive semidefinite
  have hterm : ∀ c, P.M x a * P.M x c * P.M x a = (P.M x c * P.M x a)ᴴ * (P.M x c * P.M x a) := by
    intro c
    rw [conjTranspose_mul, ← star_eq_conjTranspose, ← star_eq_conjTranspose, P.selfAdjoint,
      P.selfAdjoint, mul_assoc, mul_assoc, ← mul_assoc (P.M x c), P.projective]
  have htr : ∀ c ∈ Finset.univ.erase a, (P.M x a * P.M x c * P.M x a).trace = 0 := by
    have hnn : ∀ c ∈ Finset.univ.erase a, 0 ≤ (P.M x a * P.M x c * P.M x a).trace := by
      intro c _
      rw [hterm]
      exact (posSemidef_conjTranspose_mul_self _).trace_nonneg
    have := congrArg Matrix.trace hsum
    rw [trace_sum, trace_zero] at this
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 this
  have hba : P.M x b * P.M x a = 0 := by
    have h := htr b (Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ b⟩)
    rw [hterm] at h
    exact trace_conjTranspose_mul_self_eq_zero_iff.1 h
  have : P.M x a * P.M x b = (P.M x b * P.M x a)ᴴ := by
    rw [conjTranspose_mul, ← star_eq_conjTranspose, ← star_eq_conjTranspose, P.selfAdjoint,
      P.selfAdjoint]
  rw [this, hba, conjTranspose_zero]

/-- Merge the outcomes of a projective measurement along a map `r` of the answers: the
outcome `a` is the sum of the outcomes `a'` with `r a' = a`. -/
def merge {A' : Type*} [Fintype A'] [DecidableEq A] {n : Type*} [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A' (Matrix n n ℂ)) (r : A' → A) :
    ProjectiveMeasurement X A (Matrix n n ℂ) where
  M x a := ∑ a' ∈ Finset.univ.filter (fun a' => r a' = a), P.M x a'
  selfAdjoint x a := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun a' _ => P.selfAdjoint x a'
  projective x a := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    rw [Finset.sum_eq_single a' (fun b' _ hb' => P.mul_eq_zero_of_ne x (Ne.symm hb'))
      (fun h => absurd ha' h)]
    exact P.projective x a'
  normalized x := by
    rw [Finset.sum_fiberwise]
    exact P.normalized x

@[simp] theorem merge_M {A' : Type*} [Fintype A'] [DecidableEq A] {n : Type*} [Fintype n]
    [DecidableEq n] (P : ProjectiveMeasurement X A' (Matrix n n ℂ)) (r : A' → A) (x : X)
    (a : A) : (P.merge r).M x a = ∑ a' ∈ Finset.univ.filter (fun a' => r a' = a), P.M x a' :=
  rfl

end ProjectiveMeasurement

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-! ## Tensor-product strategies -/

namespace TensorProductStrategy

variable {G : Game X Y A B}

/-- The same data, as a strategy for another game on the same alphabets. -/
def copy (S : TensorProductStrategy G) (G' : Game X Y A B) : TensorProductStrategy G' :=
  ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA, S.PB⟩

/-- Play `S` on `G'` through relabelings of the questions (any maps) and of the answers
(equivalences). -/
def relabel {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B') (eX : X' → X) (eY : Y' → Y)
    (eA : A' ≃ A) (eB : B' ≃ B) : TensorProductStrategy G' :=
  ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA.reindex eX eA, S.PB.reindex eY eB⟩

/-- Extend the answer alphabets along embeddings, with zero operators on the new answers. -/
noncomputable def extendAnswers {A' B' : Type*} [Fintype A'] [Fintype B'] (S : TensorProductStrategy G)
    (G' : Game X Y A' B') (ιA : A ↪ A') (ιB : B ↪ B') : TensorProductStrategy G' :=
  ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA.extend ιA, S.PB.extend ιB⟩

/-- Zero extension preserves the value, whatever the decision predicate does on the new
answers: their terms vanish. -/
theorem value_extendAnswers {A' B' : Type*} [Fintype A'] [Fintype B']
    (S : TensorProductStrategy G) (G' : Game X Y A' B') (ιA : A ↪ A') (ιB : B ↪ B')
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G'.D x y (ιA a) (ιB b) = G.D x y a b) :
    (S.extendAnswers G' ιA ιB).value = S.value := by
  unfold value
  show (∑ x, ∑ y, ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) *
      (star S.ψ ⬝ᵥ (((S.PA.extend ιA).M x a' ⊗ₖ (S.PB.extend ιB).M y b') *ᵥ S.ψ)).re) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  -- restrict the outer answer sum to the range of `ιA`
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ιA)) ?_, Finset.sum_map]
  swap
  · intro a' _ ha'
    have h0 : (S.PA.extend ιA).M x a' = 0 :=
      S.PA.extend_M_of_not_mem ιA x fun ⟨a, ha⟩ => ha' (Finset.mem_map.2 ⟨a, Finset.mem_univ a, ha⟩)
    simp [h0, Matrix.zero_mulVec]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ιB)) ?_, Finset.sum_map]
  swap
  · intro b' _ hb'
    have h0 : (S.PB.extend ιB).M y b' = 0 :=
      S.PB.extend_M_of_not_mem ιB y fun ⟨b, hb⟩ => hb' (Finset.mem_map.2 ⟨b, Finset.mem_univ b, hb⟩)
    simp [h0, Matrix.zero_mulVec]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [ProjectiveMeasurement.extend_M_apply]
  rw [hμ, hD]

/-- Merge the answers along maps back to smaller alphabets. -/
def mergeAnswers {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]
    {G' : Game X Y A' B'} (S' : TensorProductStrategy G') (G : Game X Y A B) (rA : A' → A)
    (rB : B' → B) : TensorProductStrategy G :=
  ⟨S'.dA, S'.dB, S'.ψ, S'.ψ_unit, S'.PA.merge rA, S'.PB.merge rB⟩

/-- Merging can only raise the value, when every accepted tuple of the large game is
accepted after merging. -/
theorem value_le_mergeAnswers {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A]
    [DecidableEq B] {G' : Game X Y A' B'} (S' : TensorProductStrategy G') (G : Game X Y A B)
    (rA : A' → A) (rB : B' → B) (hμ : ∀ x y, G.μ x y = G'.μ x y)
    (hD : ∀ x y a' b', G'.D x y a' b' = true → G.D x y (rA a') (rB b') = true) :
    S'.value ≤ (S'.mergeAnswers G rA rB).value := by
  unfold value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  set w : A' → B' → ℝ :=
    fun a' b' => (star S'.ψ ⬝ᵥ ((S'.PA.M x a' ⊗ₖ S'.PB.M y b') *ᵥ S'.ψ)).re with hw
  have hw0 : ∀ a' b', 0 ≤ w a' b' := fun a' b' => S'.re_dotProduct_nonneg x y a' b'
  -- the merged Born-rule weight of `(a, b)` is the sum of the weights over the fibers
  have hbil : ∀ a b, (star S'.ψ ⬝ᵥ (((S'.PA.merge rA).M x a ⊗ₖ (S'.PB.merge rB).M y b) *ᵥ
      S'.ψ)).re = ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a),
        ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b), w a' b' := by
    intro a b
    have hsplit : (S'.PA.merge rA).M x a ⊗ₖ (S'.PB.merge rB).M y b =
        ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a),
          ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b), S'.PA.M x a' ⊗ₖ S'.PB.M y b' := by
      ext p q
      simp only [ProjectiveMeasurement.merge_M, Matrix.sum_apply, kroneckerMap_apply,
        Finset.sum_mul_sum]
    rw [hsplit, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  show ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) * w a' b' ≤
    ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S'.ψ ⬝ᵥ (((S'.PA.merge rA).M x a ⊗ₖ (S'.PB.merge rB).M y b) *ᵥ S'.ψ)).re
  simp_rw [hbil]
  calc ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) * w a' b'
      ≤ ∑ a', ∑ b', G.μ x y * (if G.D x y (rA a') (rB b') then 1 else 0) * w a' b' := by
        refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
        rw [hμ]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G'.μ_nonneg x y))
          (hw0 a' b')
        cases h : G'.D x y a' b' with
        | false => by_cases h' : G.D x y (rA a') (rB b') = true <;> simp [h']
        | true => rw [hD x y a' b' h]
    _ = ∑ a, ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a), ∑ b,
          ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b),
            G.μ x y * (if G.D x y (rA a') (rB b') then 1 else 0) * w a' b' := by
        rw [Finset.sum_fiberwise Finset.univ rA]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_fiberwise Finset.univ rB]
    _ = ∑ a, ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a), ∑ b,
          ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b),
            G.μ x y * (if G.D x y a b then 1 else 0) * w a' b' := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' ha' =>
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' hb' => ?_
        rw [(Finset.mem_filter.1 ha').2, (Finset.mem_filter.1 hb').2]
    _ = ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
          ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a),
            ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b), w a' b' := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]

end TensorProductStrategy

/-! ## The quantum value under transport -/

/-- Enlarging the answer alphabets by always-rejected answers does not change the quantum
value. `G'` on `A' × B'` accepts `(ιA a, ιB b)` exactly when `G` accepts `(a, b)`, and accepts
nothing off the ranges of the embeddings. -/
theorem quantumValue_extendAnswers {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A]
    [DecidableEq B] [Nonempty A] [Nonempty B] (G : Game X Y A B) (G' : Game X Y A' B')
    (ιA : A ↪ A') (ιB : B ↪ B') (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G'.D x y (ιA a) (ιB b) = G.D x y a b)
    (hD' : ∀ x y a' b', G'.D x y a' b' = true → (∃ a, ιA a = a') ∧ (∃ b, ιB b = b')) :
    quantumValue G' = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S' => ?_) (quantumValue_nonneg _)
    refine (S'.value_le_mergeAnswers G (Function.invFun ιA) (Function.invFun ιB)
      (fun x y => (hμ x y).symm) ?_).trans
      (le_ciSup (TensorProductStrategy.bddAbove_range_value G) _)
    intro x y a' b' h
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hD' x y a' b' h
    rw [Function.leftInverse_invFun ιA.injective, Function.leftInverse_invFun ιB.injective,
      ← hD]
    exact h
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    rw [← S.value_extendAnswers G' ιA ιB hμ hD]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G') _

/-! ## Synchronous strategies -/

namespace SyncStrategy

variable [DecidableEq A] {G : SynchronousGame X A}

/-- The same data, as a strategy for another synchronous game on the same alphabets. -/
def copy (S : SyncStrategy G) (G' : SynchronousGame X A) : SyncStrategy G' :=
  ⟨S.d, S.d_pos, S.P⟩

/-- Extend the answer alphabet along an embedding, with zero operators on the new answers. -/
noncomputable def extend {A' : Type*} [Fintype A'] [DecidableEq A'] (S : SyncStrategy G)
    (G' : SynchronousGame X A') (ι : A ↪ A') : SyncStrategy G' :=
  ⟨S.d, S.d_pos, S.P.extend ι⟩

/-- Zero extension preserves the value of a synchronous strategy. -/
theorem value_extend {A' : Type*} [Fintype A'] [DecidableEq A'] (S : SyncStrategy G)
    (G' : SynchronousGame X A') (ι : A ↪ A') (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G'.D x y (ι a) (ι b) = G.D x y a b) :
    (S.extend G' ι).value = S.value := by
  rw [value_eq, value_eq]
  show (∑ x, ∑ y, ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) *
      (((S.P.extend ι).M x a' * (S.P.extend ι).M y b').trace.re / (S.d : ℝ))) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ι)) ?_, Finset.sum_map]
  swap
  · intro a' _ ha'
    have h0 : (S.P.extend ι).M x a' = 0 :=
      S.P.extend_M_of_not_mem ι x fun ⟨a, ha⟩ => ha' (Finset.mem_map.2 ⟨a, Finset.mem_univ a, ha⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ι)) ?_, Finset.sum_map]
  swap
  · intro b' _ hb'
    have h0 : (S.P.extend ι).M y b' = 0 :=
      S.P.extend_M_of_not_mem ι y fun ⟨b, hb⟩ => hb' (Finset.mem_map.2 ⟨b, Finset.mem_univ b, hb⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [ProjectiveMeasurement.extend_M_apply]
  rw [hμ, hD]

/-- Zero extension preserves the PCC property. -/
theorem isPCC_extend {A' : Type*} [Fintype A'] [DecidableEq A'] {S : SyncStrategy G}
    (hS : S.IsPCC) (G' : SynchronousGame X A') (ι : A ↪ A')
    (hμ : ∀ x y, G'.μ x y = G.μ x y) : (S.extend G' ι).IsPCC := by
  intro x y hxy a' b'
  rw [hμ] at hxy
  show (S.P.extend ι).M x a' * (S.P.extend ι).M y b' = (S.P.extend ι).M y b' * (S.P.extend ι).M x a'
  by_cases ha : ∃ a, ι a = a'
  · obtain ⟨a, rfl⟩ := ha
    by_cases hb : ∃ b, ι b = b'
    · obtain ⟨b, rfl⟩ := hb
      simp only [ProjectiveMeasurement.extend_M_apply]
      exact hS x y hxy a b
    · rw [S.P.extend_M_of_not_mem ι y hb, mul_zero, zero_mul]
  · rw [S.P.extend_M_of_not_mem ι x ha, mul_zero, zero_mul]

/-- Play `S` on `G'` through relabelings of the questions (any map) and of the answers
(an equivalence). The synchronous counterpart of `TensorProductStrategy.relabel`. -/
def relabel {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A'] (S : SyncStrategy G)
    (G' : SynchronousGame X' A') (eX : X' → X) (eA : A' ≃ A) : SyncStrategy G' :=
  ⟨S.d, S.d_pos, S.P.reindex eX eA⟩

@[simp] theorem relabel_d {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A']
    (S : SyncStrategy G) (G' : SynchronousGame X' A') (eX : X' → X) (eA : A' ≃ A) :
    (S.relabel G' eX eA).d = S.d := rfl

@[simp] theorem relabel_P_M {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A']
    (S : SyncStrategy G) (G' : SynchronousGame X' A') (eX : X' → X) (eA : A' ≃ A)
    (x' : X') (a' : A') : (S.relabel G' eX eA).P.M x' a' = S.P.M (eX x') (eA a') := rfl

/-- The constant strategy: one-dimensional, always answering `a₀`. -/
def const (G : SynchronousGame X A) (a₀ : A) : SyncStrategy G where
  d := 1
  d_pos := Nat.one_pos
  P :=
    { M := fun _ a => if a = a₀ then 1 else 0
      selfAdjoint := fun _ a => by split_ifs <;> simp
      projective := fun _ a => by split_ifs <;> simp
      normalized := fun _ => by simp [Finset.sum_ite_eq'] }

end SyncStrategy

/-! ## The synchronous value under transport -/

end MIPRE


