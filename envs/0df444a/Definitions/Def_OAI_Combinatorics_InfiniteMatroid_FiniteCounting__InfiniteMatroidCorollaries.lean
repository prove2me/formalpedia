-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_FiniteCounting__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:24:00.021426+00:00
-- url     : https://prove2.me/theorems/c4192819-cb01-4daf-a9a7-1d1c851b3ef1
-- title:
--   Counting functions whose restriction along an embedding has a given property
-- statement:
--   Let $A$, $B$ and $V$ be sets, write $V^B$ for the set of all maps $B\to V$, and let $e:A\to B$ be injective.
--
--   1. **Splitting along an embedding.** The bijection
--   $$\Sigma_e:\ V^B\ \longrightarrow\ V^A\times V^{\,B\setminus e(A)},\qquad f\longmapsto\bigl(f\circ e,\ f|_{B\setminus e(A)}\bigr),$$
--   separates a function on $B$ into its pull-back along $e$ and its values off the image of $e$; its first component is $f\circ e$.
--   2. **Counting restricted conditions.** If $A$, $B$ and $V$ are finite and $P$ is any property of maps $A\to V$, then
--   $$\#\{f\in V^B:\ P(f\circ e)\}=\#\{g\in V^A:\ P(g)\}\cdot|V|^{|B|-|A|}.$$
--   3. **Density form.** For $V=\{0,1\}$ and finite $A$, $B$ this becomes the identity of real numbers
--   $$\frac{\#\{f:B\to\{0,1\}:\ P(f\circ e)\}}{2^{|B|}}=\frac{\#\{g:A\to\{0,1\}:\ P(g)\}}{2^{|A|}}.$$
--
--   Item 3 says that the proportion of Boolean functions on $B$ satisfying a condition that only inspects their values on $e(A)$ equals the proportion of Boolean functions on $A$ satisfying it; equivalently, the values of a uniformly random Boolean function at distinct points are independent fair bits. In the counterexamples $B=\{0,1\}^m$ is the set of inputs of $m$-variable Boolean functions and $e$ selects finitely many distinct inputs, and this identity is the source of the independence of the column sets.
--
--   **Formalization Note** `splitFunction e` is assembled from `Equiv.piEquivPiSubtypeProd` and `Equiv.ofInjective`, with the simp lemma `splitFunction_fst`; items 2 and 3 are `card_restriction` and `function_density_restriction`, stated with `Fintype.card` of subtypes and requiring decidable equality on $A$, $B$ and decidability of $P$. The exponent $|B|-|A|$ is natural-number subtraction, which is exact here because injectivity of $e$ gives $|A|\le|B|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/FiniteCounting.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/FiniteCounting.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroidCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Waves
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank__InfiniteMatroidCorollaries

namespace OAI

section
open Set
namespace InfiniteMatroidCounterexample

noncomputable def splitFunction {A B V : Type*} (e : A ↪ B) :
    (B → V) ≃ (A → V) × ({b : B // b ∉ Set.range e} → V) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (· ∈ Set.range e) (fun _ ↦ V)).trans
    (Equiv.prodCongr ((Equiv.ofInjective e e.injective).arrowCongr (Equiv.refl V)).symm (Equiv.refl _))

@[simp] lemma splitFunction_fst {A B V : Type*} (e : A ↪ B) (f : B → V) :
    (splitFunction e f).1 = fun a ↦ f (e a) := rfl

lemma card_restriction {A B V : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Fintype V]
    (e : A ↪ B) (P : (A → V) → Prop) [DecidablePred P] :
    Fintype.card {f : B → V // P (fun a ↦ f (e a))} =
      Fintype.card {g : A → V // P g} * Fintype.card V ^ (Fintype.card B - Fintype.card A) := by
  classical
  let fs := splitFunction (V := V) e
  have he := (fs.subtypeEquiv (p := fun f ↦ P (fun a ↦ f (e a)))
      (q := fun f ↦ P f.1) (fun f ↦ by simp [fs])).trans Equiv.prodSubtypeFstEquivSubtypeProd
  have hc : Fintype.card {b : B // b ∈ Set.range e} = Fintype.card A :=
    (Fintype.card_congr (Equiv.ofInjective e e.injective)).symm
  rw [Fintype.card_congr he, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, hc]

lemma function_density_restriction {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (P : (A → Bool) → Prop) [DecidablePred P] :
    (Fintype.card {f : B → Bool // P (fun a ↦ f (e a))} : ℝ) / Fintype.card (B → Bool) =
      (Fintype.card {g : A → Bool // P g} : ℝ) / Fintype.card (A → Bool) := by
  rw [card_restriction]
  simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hle : Fintype.card A ≤ Fintype.card B := Fintype.card_le_of_injective e e.injective
  have heq : (2:ℝ) ^ Fintype.card B = 2 ^ Fintype.card A * 2 ^ (Fintype.card B - Fintype.card A) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [heq]
  field_simp

end InfiniteMatroidCounterexample
end

end OAI


