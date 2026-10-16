-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
-- name    : OAI_RepresentationTheory_FoulkesHowe_DegreeOne
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:13:25.819438+00:00
-- url     : https://prove2.me/theorems/a4386e8f-9b18-41d9-8f7c-75120a47dbf1
-- title:
--   The degree-one symmetric power $\mathrm{Sym}^1 V$ is canonically isomorphic to $V$
-- statement:
--   Let $V$ be a complex vector space, $S(V)$ its symmetric algebra over $\mathbb{C}$, and $\iota:V\to S(V)$ the canonical linear map onto the degree-one generators. For $n\in\mathbb{N}$ and $v_0,\dots,v_{n-1}\in V$ write $[v_0,\dots,v_{n-1}]=\iota(v_0)\iota(v_1)\cdots\iota(v_{n-1})$, and let $\mathrm{Sym}^n V\subseteq S(V)$ be the linear span of all such products. The file identifies the case $n=1$.
--
--   1. The canonical map $\iota:V\to S(V)$ is injective.
--   2. A one-factor product is a generator, $[v_0]=\iota(v_0)$, and consequently $\mathrm{Sym}^1 V=\iota(V)$ is the range of $\iota$.
--   3. The map $j:V\to\mathrm{Sym}^1 V$, $j(v)=\iota(v)$, obtained by restricting the codomain of $\iota$, is a bijective linear map.
--   4. Hence there is a linear isomorphism $\varepsilon:\mathrm{Sym}^1 V\to V$, the inverse of $j$, satisfying
--   $$\varepsilon\bigl([v_0]\bigr)=v_0\qquad\text{and}\qquad\varepsilon^{-1}(v)=[v]\qquad\text{for all }v_0,v\in V.$$
--
--   This identification lets statements about plethysms $\mathrm{Sym}^a(\mathrm{Sym}^b V)$ be compared with simpler spaces in the degenerate cases $a=1$ or $b=1$, where one of the two symmetric powers is just the underlying space.
--
--   **Formalization Note** `SymPow 1 V` is a subtype of the symmetric algebra. `symPowOneIntro V` is the corestriction of `SymmetricAlgebra.ι` to it, `symPowOneEquiv V` is the inverse of the linear equivalence built from its bijectivity, and the simp lemmas `symPowOneEquiv_symm_apply` and `symPowOneEquiv_symMonomial` are the two displayed formulas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/DegreeOne.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/DegreeOne.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model

namespace OAI

noncomputable section
universe u
namespace Problem346

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

lemma symmetricAlgebra_ι_injective :
    Function.Injective (SymmetricAlgebra.ι ℂ V) := by
  let : Module ℂᵐᵒᵖ V := Module.compHom _ ((RingHom.id ℂ).fromOpposite mul_comm)
  have : IsCentralScalar ℂ V := ⟨fun _ _ => rfl⟩
  intro x y h
  have h' := congrArg (SymmetricAlgebra.lift (TrivSqZeroExt.inrHom ℂ V)) h
  apply TrivSqZeroExt.inr_injective (R := ℂ)
  simpa using h'

@[simp] lemma symMonomialRaw_one (v : Fin 1 → V) :
    symMonomialRaw 1 V v = SymmetricAlgebra.ι ℂ V (v 0) := by
  simp [symMonomialRaw]

lemma symPowSubmodule_one :
    symPowSubmodule 1 V = LinearMap.range (SymmetricAlgebra.ι ℂ V) := by
  have h : Set.range (symMonomialRaw 1 V) =
      Set.range (SymmetricAlgebra.ι ℂ V) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v 0, (symMonomialRaw_one V v).symm⟩
    · rintro ⟨v, rfl⟩
      exact ⟨fun _ => v, symMonomialRaw_one V (fun _ => v)⟩
  rw [symPowSubmodule, h]
  exact Submodule.span_eq (LinearMap.range (SymmetricAlgebra.ι ℂ V))

/-- The canonical inclusion of a vector into the degree-one symmetric power. -/
def symPowOneIntro : V →ₗ[ℂ] SymPow 1 V :=
  (SymmetricAlgebra.ι ℂ V).codRestrict (symPowSubmodule 1 V) (by
    intro v
    rw [symPowSubmodule_one]
    exact ⟨v, rfl⟩)

@[simp] lemma symPowOneIntro_coe (v : V) :
    (symPowOneIntro V v : SymmetricAlgebra ℂ V) = SymmetricAlgebra.ι ℂ V v := rfl

lemma symPowOneIntro_bijective : Function.Bijective (symPowOneIntro V) := by
  constructor
  · intro x y h
    apply symmetricAlgebra_ι_injective V
    exact congrArg Subtype.val h
  · intro x
    have hx := x.property
    have hx' : (x : SymmetricAlgebra ℂ V) ∈ LinearMap.range (SymmetricAlgebra.ι ℂ V) := by
      simpa only [symPowSubmodule_one] using hx
    rcases hx' with ⟨v, hv⟩
    exact ⟨v, Subtype.ext hv⟩

/-- The degree-one symmetric power is canonically the original vector space. -/
def symPowOneEquiv : SymPow 1 V ≃ₗ[ℂ] V :=
  (LinearEquiv.ofBijective (symPowOneIntro V) (symPowOneIntro_bijective V)).symm

@[simp] lemma symPowOneEquiv_symm_apply (v : V) :
    (symPowOneEquiv V).symm v = symMonomial 1 V (fun _ => v) := by
  apply Subtype.ext
  exact (symMonomialRaw_one V (fun _ => v)).symm

@[simp] lemma symPowOneEquiv_symMonomial (v : Fin 1 → V) :
    symPowOneEquiv V (symMonomial 1 V v) = v 0 := by
  apply (symPowOneEquiv V).symm.injective
  simp only [LinearEquiv.symm_apply_apply, symPowOneEquiv_symm_apply]
  apply Subtype.ext
  simp only [symMonomial, symMonomialRaw_one]

end Problem346

end

end OAI


