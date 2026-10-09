-- Prove2me | Definitions.Def_SidorenkoFiniteGeometryCertificates06
-- name    : SidorenkoFiniteGeometryCertificates06
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T05:49:23.844895+00:00
-- url     : https://prove2.me/theorems/78f4ddcd-0724-4c21-a08b-f5841b6e1e72
-- title:
--   Orbits data and explicit proof certificate interfaces
-- statement:
--   This interface records the data constructions and fully quantified propositions of Orbits in the cited source. For every source proposition $P_\ell$, let $C_\ell$ be its one-field proof record:
--   $$C_\ell=\{h:P_\ell\}.$$
--   The carriers of the quantified vector spaces and finite state sets are restricted to the lowest type universe. Each construction requiring an earlier proposition is parameterized by its proof record. A projection recovers the recorded proof when that record is supplied; no records are instantiated by this interface.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Orbits.lean, source definitions and theorem statements, specialized to Type 0.

import Mathlib
import Definitions.Def_SidorenkoFiniteGeometryCertificates05
set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0182 : Prop where
  proof : ((∀ {A B : Type} [Finite A] [Finite B]
        (f : A → B) (m : ℕ) (h : ∀ b, Nat.card {a : A // f a = b} ≤ m),
    Nat.card A ≤ Nat.card B * m))

theorem card_le_card_mul_of_fibers [h : OAI.SidorenkoCounterexample.ProofCertificate_0182] : ((∀ {A B : Type} [Finite A] [Finite B]
      (f : A → B) (m : ℕ) (h : ∀ b, Nat.card {a : A // f a = b} ≤ m),
  Nat.card A ≤ Nat.card B * m)) := @OAI.SidorenkoCounterexample.ProofCertificate_0182.proof h
end

section NormSphere
variable {K E : Type} [Field K] [Fintype K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0183 : Prop where
  proof : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (a : K),
    Nat.card {x : K // x^2 = a} ≤ 2))

theorem square_fiber_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0183] : (∀ {K : Type} [inst : Field K] [inst : Fintype K], (∀ (a : K),
  Nat.card {x : K // x^2 = a} ≤ 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0183.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0184 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup E] [inst : @_root_.Module K E _ _]
      [inst : Finite E], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
        (x : E) (hx : B x x ≠ 0) (a : K),
    Nat.card {v : E // B v v = a} ≤
          2 * Nat.card (B.orthogonal (K ∙ x))))

theorem norm_sphere_count [h : OAI.SidorenkoCounterexample.ProofCertificate_0184] : (∀ {K E : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup E] [inst : @_root_.Module K E _ _]
    [inst : Finite E], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
      (x : E) (hx : B x x ≠ 0) (a : K),
  Nat.card {v : E // B v v = a} ≤
        2 * Nat.card (B.orthogonal (K ∙ x)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0184.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0185 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup E] [inst_3 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _] [inst : Finite E], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
        (x : E) (hx : B x x ≠ 0) (a : K),
    Nat.card {v : E // B v v = a} ≤ 2 * Fintype.card K ^ (finrank K E - 1)))

theorem norm_sphere_count_pow [h : OAI.SidorenkoCounterexample.ProofCertificate_0185] : (∀ {K E : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup E] [inst_3 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _] [inst : Finite E], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
      (x : E) (hx : B x x ≠ 0) (a : K),
  Nat.card {v : E // B v v = a} ≤ 2 * Fintype.card K ^ (finrank K E - 1))) := @OAI.SidorenkoCounterexample.ProofCertificate_0185.proof h
end

end NormSphere
section Isometries
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
def BilinAut (B : LinearMap.BilinForm K E) :=
  {e : E ≃ₗ[K] E // ∀ x y, B (e x) (e y) = B x y}

instance (B : LinearMap.BilinForm K E) [Finite E] : Finite (BilinAut B) := by
  apply Finite.of_injective (fun e : BilinAut B => (e.val : E → E))
  intro e f h
  apply Subtype.ext
  exact LinearEquiv.ext (congrFun h)
noncomputable def restrictBilinAut (B : LinearMap.BilinForm K E)
    (x : E) (e : BilinAut B) (hfix : e.val x = x) :
    BilinAut (B.restrict (B.orthogonal (K ∙ x))) := by
  let P := B.orthogonal (K ∙ x)
  have hp : ∀ z ∈ P, e.val z ∈ P := by
    intro z hz a ha
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp ha
    have hh : B x (e.val z) = 0 := by
      calc
        _ = B (e.val x) (e.val z) := by rw [hfix]
        _ = B x z := e.property x z
        _ = 0 := hz x (Submodule.mem_span_singleton_self x)
    simp [hh]
  let g : P →ₗ[K] P := e.val.toLinearMap.restrict hp
  have hg : Function.Injective g := by
    intro z w h
    apply Subtype.ext
    exact e.val.injective (congrArg Subtype.val h)
  let f : P ≃ₗ[K] P := LinearEquiv.ofBijective g
    ⟨hg,LinearMap.injective_iff_surjective.mp hg⟩
  refine ⟨f,?_⟩
  intro z w
  exact e.property z.val w.val

section
attribute [local instance] certificateFintype
class ProofCertificate_0186 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (B : LinearMap.BilinForm K E)
        (x : E) (e : BilinAut B) (hfix : e.val x = x)
        (z : B.orthogonal (K ∙ x)),
    ((restrictBilinAut B x e hfix).val z).val = e.val z.val))

@[simp]
theorem restrictBilinAut_apply [h : OAI.SidorenkoCounterexample.ProofCertificate_0186] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (B : LinearMap.BilinForm K E)
      (x : E) (e : BilinAut B) (hfix : e.val x = x)
      (z : B.orthogonal (K ∙ x)),
  ((restrictBilinAut B x e hfix).val z).val = e.val z.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0186.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0187 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (B : LinearMap.BilinForm K E)
        (x : E) (hx : B x x ≠ 0),
    Function.Injective (fun e : {e : BilinAut B // e.val x = x} =>
          restrictBilinAut B x e.val e.property)))

theorem restrictBilinAut_injective [h : OAI.SidorenkoCounterexample.ProofCertificate_0187] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (B : LinearMap.BilinForm K E)
      (x : E) (hx : B x x ≠ 0),
  Function.Injective (fun e : {e : BilinAut B // e.val x = x} =>
        restrictBilinAut B x e.val e.property))) := @OAI.SidorenkoCounterexample.ProofCertificate_0187.proof h
end

noncomputable def relativeBilinAut (B : LinearMap.BilinForm K E)
    (e f : BilinAut B) : BilinAut B :=
  ⟨e.val.trans f.val.symm,by
    intro x y
    have hf := f.property (f.val.symm (e.val x)) (f.val.symm (e.val y))
    simp only [LinearEquiv.apply_symm_apply] at hf
    exact hf.symm.trans (e.property x y)⟩

section
attribute [local instance] certificateFintype
class ProofCertificate_0188 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (B : LinearMap.BilinForm K E) (f : BilinAut B),
    Function.Injective (fun e => relativeBilinAut B e f)))

theorem relativeBilinAut_injective [h : OAI.SidorenkoCounterexample.ProofCertificate_0188] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (B : LinearMap.BilinForm K E) (f : BilinAut B),
  Function.Injective (fun e => relativeBilinAut B e f))) := @OAI.SidorenkoCounterexample.ProofCertificate_0188.proof h
end

variable [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0189 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _] [inst : Finite E], (∀ (B : LinearMap.BilinForm K E) (x y : E)
        (hx : B x x ≠ 0),
    Nat.card {e : BilinAut B // e.val x = y} ≤
          Nat.card (BilinAut (B.restrict (B.orthogonal (K ∙ x))))))

theorem bilinAut_eval_fiber_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0189] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _] [inst : Finite E], (∀ (B : LinearMap.BilinForm K E) (x y : E)
      (hx : B x x ≠ 0),
  Nat.card {e : BilinAut B // e.val x = y} ≤
        Nat.card (BilinAut (B.restrict (B.orthogonal (K ∙ x)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0189.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0190 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _] [inst : Finite E], (∀ (B : LinearMap.BilinForm K E) (x : E) (hx : B x x ≠ 0),
    Nat.card (BilinAut B) ≤ Nat.card {y : E // B y y = B x x} *
          Nat.card (BilinAut (B.restrict (B.orthogonal (K ∙ x))))))

theorem bilinAut_step [h : OAI.SidorenkoCounterexample.ProofCertificate_0190] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _] [inst : Finite E], (∀ (B : LinearMap.BilinForm K E) (x : E) (hx : B x x ≠ 0),
  Nat.card (BilinAut B) ≤ Nat.card {y : E // B y y = B x x} *
        Nat.card (BilinAut (B.restrict (B.orthogonal (K ∙ x)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0190.proof h
end

variable [Fintype K] [Invertible (2 : K)]
section
attribute [local instance] certificateFintype
class ProofCertificate_0191 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] [inst_4 : Finite E] [inst_5 : Fintype K]
      [inst : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
        (hB : B.Nondegenerate),
    Nat.card (BilinAut B) ≤ 2 ^ finrank K E * Fintype.card K ^ (finrank K E).choose 2))

theorem bilinAut_card_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0191] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] [inst_4 : Finite E] [inst_5 : Fintype K]
    [inst : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
      (hB : B.Nondegenerate),
  Nat.card (BilinAut B) ≤ 2 ^ finrank K E * Fintype.card K ^ (finrank K E).choose 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0191.proof h
end

end Isometries
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FormOrbits
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
noncomputable def linearAutTuple : (E ≃ₗ[K] E) →
    {v : Fin (finrank K E) → E // LinearIndependent K v} := fun e =>
  ⟨fun i => e (finBasis K E i), (finBasis K E).linearIndependent.map' e.toLinearMap
    (LinearMap.ker_eq_bot.mpr e.injective)⟩

section
attribute [local instance] certificateFintype
class ProofCertificate_0192 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (Function.Bijective (linearAutTuple (K := K) (E := E))))

theorem linearAutTuple_bijective [h : OAI.SidorenkoCounterexample.ProofCertificate_0192] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (Function.Bijective (linearAutTuple (K := K) (E := E)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0192.proof h
end

variable [Fintype K] [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0193 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _] [inst : Fintype K] [inst : Finite E], (Nat.card (E ≃ₗ[K] E) =
        ∏ i : Fin (finrank K E), (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val)))

theorem linearAut_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0193] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _] [inst : Fintype K] [inst : Finite E], (Nat.card (E ≃ₗ[K] E) =
      ∏ i : Fin (finrank K E), (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0193.proof h
end

abbrev FormOrbit (B : LinearMap.BilinForm K E) :=
  {C : LinearMap.BilinForm K E // ∃ e : E ≃ₗ[K] E, C = B.comp e.toLinearMap e.toLinearMap}

instance linearAut_finite : Finite (E ≃ₗ[K] E) :=
  Finite.of_injective (fun e : E ≃ₗ[K] E => (e : E → E))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

instance formOrbit_finite (B : LinearMap.BilinForm K E) : Finite (FormOrbit B) :=
  Finite.of_injective (fun C : FormOrbit B => fun x y => C.val x y) (by
    intro C D h
    apply Subtype.ext
    ext x y
    exact congrFun (congrFun h x) y)

def formOrbitMap (B : LinearMap.BilinForm K E) (e : E ≃ₗ[K] E) : FormOrbit B :=
  ⟨B.comp e.toLinearMap e.toLinearMap,⟨e,rfl⟩⟩

section
attribute [local instance] certificateFintype
class ProofCertificate_0194 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Finite E], (∀ (B : LinearMap.BilinForm K E) (C : FormOrbit B),
    Nat.card {e : E ≃ₗ[K] E // formOrbitMap B e = C} ≤ Nat.card (BilinAut B)))

theorem formOrbit_fiber_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0194] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Finite E], (∀ (B : LinearMap.BilinForm K E) (C : FormOrbit B),
  Nat.card {e : E ≃ₗ[K] E // formOrbitMap B e = C} ≤ Nat.card (BilinAut B))) := @OAI.SidorenkoCounterexample.ProofCertificate_0194.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0195 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype K]
      [inst : Finite E], (∀ (B : LinearMap.BilinForm K E),
    Nat.card (E ≃ₗ[K] E) ≤ Nat.card (FormOrbit B) * Nat.card (BilinAut B)))

theorem formOrbit_card_mul_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0195] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype K]
    [inst : Finite E], (∀ (B : LinearMap.BilinForm K E),
  Nat.card (E ≃ₗ[K] E) ≤ Nat.card (FormOrbit B) * Nat.card (BilinAut B))) := @OAI.SidorenkoCounterexample.ProofCertificate_0195.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0196 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _] [inst : Fintype K] [inst : Finite E], (Fintype.card K ^ (finrank K E * finrank K E) ≤
        2 ^ finrank K E * Nat.card (E ≃ₗ[K] E)))

theorem linearAut_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0196] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _] [inst : Fintype K] [inst : Finite E], (Fintype.card K ^ (finrank K E * finrank K E) ≤
      2 ^ finrank K E * Nat.card (E ≃ₗ[K] E))) := @OAI.SidorenkoCounterexample.ProofCertificate_0196.proof h
end

variable [Invertible (2 : K)]
section
attribute [local instance] certificateFintype
class ProofCertificate_0197 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] [inst_4 : Fintype K] [inst_5 : Finite E]
      [inst : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
        (hB : B.Nondegenerate),
    Fintype.card K ^ (finrank K E+1).choose 2 ≤
          4 ^ finrank K E * Nat.card (FormOrbit B)))

theorem formOrbit_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0197] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] [inst_4 : Fintype K] [inst_5 : Finite E]
    [inst : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)], (∀ (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
      (hB : B.Nondegenerate),
  Fintype.card K ^ (finrank K E+1).choose 2 ≤
        4 ^ finrank K E * Nat.card (FormOrbit B))) := @OAI.SidorenkoCounterexample.ProofCertificate_0197.proof h
end

end FormOrbits
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TransverseForms
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0198 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hs : B.IsSymm),
    canonicalSymplectic.orthogonal B.graph = B.graph))

theorem fullGraph_selforthogonal [h : OAI.SidorenkoCounterexample.ProofCertificate_0198] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hs : B.IsSymm),
  canonicalSymplectic.orthogonal B.graph = B.graph)) := @OAI.SidorenkoCounterexample.ProofCertificate_0198.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0199 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (Function.Injective
        (fun B : LinearMap.BilinForm K V => B.graph)))

theorem fullGraph_injective [h : OAI.SidorenkoCounterexample.ProofCertificate_0199] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (Function.Injective
      (fun B : LinearMap.BilinForm K V => B.graph))) := @OAI.SidorenkoCounterexample.ProofCertificate_0199.proof h
end

def formCoordinateEquiv (g : V ≃ₗ[K] V) :
    (V × Module.Dual K V) ≃ₗ[K] (V × Module.Dual K V) :=
  g.symm.prodCongr g.dualMap

section
attribute [local instance] certificateFintype
class ProofCertificate_0200 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (g : V ≃ₗ[K] V) (x y : V × Module.Dual K V),
    canonicalSymplectic (formCoordinateEquiv g x) (formCoordinateEquiv g y) =
          canonicalSymplectic x y))

theorem formCoordinateEquiv_isometry [h : OAI.SidorenkoCounterexample.ProofCertificate_0200] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (g : V ≃ₗ[K] V) (x y : V × Module.Dual K V),
  canonicalSymplectic (formCoordinateEquiv g x) (formCoordinateEquiv g y) =
        canonicalSymplectic x y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0200.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0201 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (g : V ≃ₗ[K] V),
    B.graph.map (formCoordinateEquiv g).toLinearMap = (B.comp g.toLinearMap g.toLinearMap).graph))

theorem fullGraph_congruence [h : OAI.SidorenkoCounterexample.ProofCertificate_0201] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (g : V ≃ₗ[K] V),
  B.graph.map (formCoordinateEquiv g).toLinearMap = (B.comp g.toLinearMap g.toLinearMap).graph)) := @OAI.SidorenkoCounterexample.ProofCertificate_0201.proof h
end

end TransverseForms
section TransverseTripleCoordinates
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0202 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (L M N : Submodule K E) (hL : ω.orthogonal L = L)
        (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥),
    ∃ (e : (L × Module.Dual K L) ≃ₗ[K] E) (B : LinearMap.BilinForm K L),
          B.IsSymm ∧ B.Nondegenerate ∧
          (∀ x, e x ∈ L ↔ x.2 = 0) ∧ (∀ x, e x ∈ M ↔ x.1 = 0) ∧
          (∀ x, e x ∈ N ↔ x.2 = B x.1) ∧
          (∀ x y, ω (e x) (e y) = canonicalSymplectic x y)))

theorem exists_transverse_triple_form [h : OAI.SidorenkoCounterexample.ProofCertificate_0202] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (L M N : Submodule K E) (hL : ω.orthogonal L = L)
      (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥),
  ∃ (e : (L × Module.Dual K L) ≃ₗ[K] E) (B : LinearMap.BilinForm K L),
        B.IsSymm ∧ B.Nondegenerate ∧
        (∀ x, e x ∈ L ↔ x.2 = 0) ∧ (∀ x, e x ∈ M ↔ x.1 = 0) ∧
        (∀ x, e x ∈ N ↔ x.2 = B x.1) ∧
        (∀ x y, ω (e x) (e y) = canonicalSymplectic x y))) := @OAI.SidorenkoCounterexample.ProofCertificate_0202.proof h
end

end TransverseTripleCoordinates
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FixedPairOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : Submodule K E)
abbrev FixedPairOrbit := {N' : Submodule K E //
  ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
    L.map e.toLinearMap = L ∧ M.map e.toLinearMap = M ∧ N.map e.toLinearMap = N'}

section
attribute [local instance] certificateFintype
class ProofCertificate_0203 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @Submodule K E _ _ _), (∀ (hN : ω.orthogonal N = N)
        (N' : FixedPairOrbit ω L M N),
    ω.orthogonal N'.val = N'.val))

theorem fixedPairOrbit_selforthogonal [h : OAI.SidorenkoCounterexample.ProofCertificate_0203] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @Submodule K E _ _ _), (∀ (hN : ω.orthogonal N = N)
      (N' : FixedPairOrbit ω L M N),
  ω.orthogonal N'.val = N'.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0203.proof h
end

variable [FiniteDimensional K E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0204 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @Submodule K E _ _ _) [inst : @FiniteDimensional K E _ _ _], (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥),
    ∃ B : LinearMap.BilinForm K L, B.IsSymm ∧ B.Nondegenerate ∧
          ∃ f : FormOrbit B → FixedPairOrbit ω L M N, Function.Injective f))

theorem fixedPairOrbit_form_injection [h : OAI.SidorenkoCounterexample.ProofCertificate_0204] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @Submodule K E _ _ _) [inst : @FiniteDimensional K E _ _ _], (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥),
  ∃ B : LinearMap.BilinForm K L, B.IsSymm ∧ B.Nondegenerate ∧
        ∃ f : FormOrbit B → FixedPairOrbit ω L M N, Function.Injective f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0204.proof h
end

variable [Fintype K] [Finite E] [Invertible (2 : K)]
section
attribute [local instance] certificateFintype
class ProofCertificate_0205 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @Submodule K E _ _ _) [inst_3 : @FiniteDimensional K E _ _ _]
      [inst_4 : Fintype K] [inst_5 : Finite E] [inst : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)], (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥),
    Fintype.card K ^ (finrank K L+1).choose 2 ≤
          4 ^ finrank K L * Nat.card (FixedPairOrbit ω L M N)))

theorem fixedPairOrbit_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0205] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @Submodule K E _ _ _) [inst_3 : @FiniteDimensional K E _ _ _]
    [inst_4 : Fintype K] [inst_5 : Finite E] [inst : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)], (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥),
  Fintype.card K ^ (finrank K L+1).choose 2 ≤
        4 ^ finrank K L * Nat.card (FixedPairOrbit ω L M N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0205.proof h
end

end FixedPairOrbit
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCountingBounds
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0206 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : Finite V], (Nat.card (Lagrangian (K := K) (V := V)) =
          ∑ k : Fin (finrank K V+1), Nat.card (DimSubspace K V k.val) *
            Fintype.card K ^ (k.val+1).choose 2))

theorem lagrangian_card_by_dimension [h : OAI.SidorenkoCounterexample.ProofCertificate_0206] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : Finite V], (Nat.card (Lagrangian (K := K) (V := V)) =
        ∑ k : Fin (finrank K V+1), Nat.card (DimSubspace K V k.val) *
          Fintype.card K ^ (k.val+1).choose 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0206.proof h
end

noncomputable def lagrangianConstant (n : ℕ) : ℝ := (n+1) * 2^n

section
attribute [local instance] certificateFintype
class ProofCertificate_0207 : Prop where
  proof : ((∀ (n : ℕ),
    0 < lagrangianConstant n))

theorem lagrangianConstant_pos [h : OAI.SidorenkoCounterexample.ProofCertificate_0207] : ((∀ (n : ℕ),
  0 < lagrangianConstant n)) := @OAI.SidorenkoCounterexample.ProofCertificate_0207.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0208 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : Finite V], ((Nat.card (Lagrangian (K := K) (V := V)) : ℝ) ≤
          lagrangianConstant (finrank K V) * (Fintype.card K : ℝ)^((finrank K V+1).choose 2)))

theorem lagrangian_card_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0208] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : Finite V], ((Nat.card (Lagrangian (K := K) (V := V)) : ℝ) ≤
        lagrangianConstant (finrank K V) * (Fintype.card K : ℝ)^((finrank K V+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0208.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0209 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : Finite V], ((Fintype.card K : ℝ)^((finrank K V+1).choose 2) ≤
          Nat.card (Lagrangian (K := K) (V := V))))

theorem lagrangian_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0209] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : Finite V], ((Fintype.card K : ℝ)^((finrank K V+1).choose 2) ≤
        Nat.card (Lagrangian (K := K) (V := V)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0209.proof h
end

end UniformCountingBounds
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullTripleOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev SymplecticLagrangian := {L : Submodule K E // ω.orthogonal L = L}

abbrev OrderedTransversePair := {p : SymplecticLagrangian ω × SymplecticLagrangian ω //
  p.1.val ⊓ p.2.val = ⊥}

abbrev OrderedTripleOrbit (L M N : Submodule K E) :=
  {p : Submodule K E × Submodule K E × Submodule K E //
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = p.1 ∧ M.map e.toLinearMap = p.2.1 ∧
      N.map e.toLinearMap = p.2.2}

variable [FiniteDimensional K E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0210 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : @FiniteDimensional K E _ _ _], (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (L M N : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
        (hLM : L ⊓ M = ⊥),
    ∃ f : OrderedTransversePair ω × FixedPairOrbit ω L M N → OrderedTripleOrbit ω L M N,
          Function.Injective f))

theorem orderedTripleOrbit_pair_injection [h : OAI.SidorenkoCounterexample.ProofCertificate_0210] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : @FiniteDimensional K E _ _ _], (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (L M N : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
      (hLM : L ⊓ M = ⊥),
  ∃ f : OrderedTransversePair ω × FixedPairOrbit ω L M N → OrderedTripleOrbit ω L M N,
        Function.Injective f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0210.proof h
end

end FullTripleOrbit
section CanonicalTripleMass
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
local notation "ω" => (canonicalSymplectic (K := K) (V := V))
section
attribute [local instance] certificateFintype
class ProofCertificate_0211 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : Finite V], (∀ (h2 : (2 : K) ≠ 0) (A : Lagrangian (K := K) (V := V)),
    Nat.card {B : Lagrangian (K := K) (V := V) // A.val ⊓ B.val = ⊥} =
          Fintype.card K^((finrank K V+1).choose 2)))

theorem transverse_to_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0211] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : Finite V], (∀ (h2 : (2 : K) ≠ 0) (A : Lagrangian (K := K) (V := V)),
  Nat.card {B : Lagrangian (K := K) (V := V) // A.val ⊓ B.val = ⊥} =
        Fintype.card K^((finrank K V+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0211.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0212 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : Finite V], (∀ (h2 : (2 : K) ≠ 0),
    Nat.card (OrderedTransversePair (canonicalSymplectic (K := K) (V := V))) = Nat.card (Lagrangian (K := K) (V := V)) *
          Fintype.card K^((finrank K V+1).choose 2)))

theorem orderedTransversePair_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0212] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : Finite V], (∀ (h2 : (2 : K) ≠ 0),
  Nat.card (OrderedTransversePair (canonicalSymplectic (K := K) (V := V))) = Nat.card (Lagrangian (K := K) (V := V)) *
        Fintype.card K^((finrank K V+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0212.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0213 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : Finite V], (∀ [Invertible (2 : K)]
        (L M N : Lagrangian (K := K) (V := V))
        (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥),
    Nat.card (Lagrangian (K := K) (V := V)) *
            (Fintype.card K^((finrank K V+1).choose 2)) ^ 2 ≤
          4^finrank K V * Nat.card (OrderedTripleOrbit (canonicalSymplectic (K := K) (V := V)) L.val M.val N.val)))

theorem orderedTransverseTriple_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0213] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : Finite V], (∀ [Invertible (2 : K)]
      (L M N : Lagrangian (K := K) (V := V))
      (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥),
  Nat.card (Lagrangian (K := K) (V := V)) *
          (Fintype.card K^((finrank K V+1).choose 2)) ^ 2 ≤
        4^finrank K V * Nat.card (OrderedTripleOrbit (canonicalSymplectic (K := K) (V := V)) L.val M.val N.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0213.proof h
end

end CanonicalTripleMass
end SidorenkoCounterexample
end OAI


