-- Prove2me | Definitions.Def_MasulloGRH_LocallyConvex
-- name    : MasulloGRH_LocallyConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:21:47.148712+00:00
-- url     : https://prove2.me/theorems/a7baf879-cadb-40e2-97d5-ebf25452032d
-- title:
--   Locally convex spaces: complete, Fréchet, reflexive, Montel, nuclear, (strict) LF-spaces, tensor product topologies
-- statement:
--   This file fixes the vocabulary of locally convex spaces used throughout the mission. All vector spaces are complex.
--
--   1. A topology on $E$ is **locally convex** if it is defined by a family of seminorms. $E$ is a **Hausdorff locally convex space** if in addition it is Hausdorff.
--   2. A filter on $E$ is **Cauchy** if for every $0$-neighbourhood $U$ it contains a set $A$ with $A-A\subset U$. $E$ is **complete** if it is Hausdorff and every Cauchy filter (equivalently, every Cauchy net) converges; **quasi-complete** if it is Hausdorff and every Cauchy filter containing a bounded set converges, i.e. closed bounded subsets are complete.
--   3. $E$ is a **Fréchet space** if it is locally convex, complete and metrizable.
--   4. $E$ is **bornological** if every seminorm that is bounded on bounded sets is continuous. $E$ carries the **finest locally convex topology** if its topology is the finest among all locally convex topologies on $E$.
--   5. The **strong dual** $E'_\beta$ is the space of continuous linear functionals with the topology of uniform convergence on bounded sets. $E$ is **reflexive** if the canonical map $E\to(E'_\beta)'_\beta$ is a topological isomorphism: every continuous linear functional on $E'_\beta$ is the evaluation at a unique point of $E$, and the topology of $E$ is the topology of uniform convergence on the bounded subsets of $E'_\beta$.
--   6. $E$ is a **Montel space** if it is a Hausdorff locally convex space in which every closed bounded subset is compact and which is reflexive.
--   7. On the algebraic tensor product $E\otimes F$:
--      - the **projective topology** ($\pi$) is the finest locally convex topology for which $E\times F\to E\otimes F$ is continuous;
--      - the **inductive topology** ($\iota$) is the finest locally convex topology for which $E\times F\to E\otimes F$ is separately continuous;
--      - the **injective topology** ($\varepsilon$) is the topology of uniform convergence on the sets $A\times B$ with $A\subset E'$, $B\subset F'$ equicontinuous, a tensor $u$ being viewed as the function $(x',y')\mapsto(x'\otimes y')(u)$.
--   8. $E$ is **nuclear** if it is a Hausdorff locally convex space and for every Hausdorff locally convex space $F$ the identity map $E\otimes_\pi F\to E\otimes_\varepsilon F$ is a topological isomorphism.
--   9. $E$ is a **strict LF-space** if it is the union of an increasing sequence of subspaces $E_n$, each a Fréchet space for the induced topology, and $E$ carries the locally convex inductive limit topology: the finest locally convex topology for which all inclusions $E_n\to E$ are continuous. It is a **strict inductive limit of nuclear Fréchet spaces** if moreover every $E_n$ is nuclear. $E$ is an **LF-space** if it is Hausdorff and is the locally convex inductive limit of a sequence of Fréchet spaces $E_n$ with injective continuous transition maps.
--   10. A linear map is a **linear topological isomorphism** if it is bijective, continuous and open, and a **linear topological embedding** if it is a homeomorphism onto its image. A map $f\colon E\to F$ has the **bounded lifting property** if every bounded subset of $F$ is contained in the image of a bounded subset of $E$.
--
--   Barrelled spaces are Mathlib's `BarrelledSpace`.
--
--   **Formalization Note** Every notion is a property of the topology of $E$; no compatibility with the vector space structure is assumed in the definitions. In item 8 the test spaces $F$ range over the universe of $E$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C: Definition C.1.3.1 (p. 659); §C.1.4, Example C.1.4.6 (pp. 660–663); Definition C.1.5.2 and the paragraph on strict inductive limits (p. 664); Definition C.1.5.9 (p. 667); Definitions C.2.1.4–C.2.1.5 (p. 671); §C.2.3; Definition C.2.4.1 (p. 685)

import Mathlib

/-!
# Locally convex spaces: the vocabulary of Appendix C

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix C:
Definition C.1.3.1 (p. 659), §C.1.4 (pp. 660–663, in particular Example C.1.4.6), Definition C.1.5.2
and the paragraph on strict inductive limits (p. 664), Definition C.1.5.9 (p. 667),
Definitions C.2.1.4 and C.2.1.5 (p. 671), §C.2.3 (tensor product topologies), Definition C.2.4.1
(p. 685).

All vector spaces are over `ℂ`.  A topological property of a space `E` is a property of the
topology carried by `E`; no instance beyond `TopologicalSpace E` is assumed.
-/

set_option warn.classDefReducibility false

namespace MasulloGRH

open TensorProduct Topology

noncomputable section

universe u

section basic

variable (E : Type u) [AddCommGroup E] [Module ℂ E]

/-- `t` is a locally convex vector space topology on `E`: it is the topology defined by some
family of seminorms on `E`. -/
def IsLocallyConvexTopology (t : TopologicalSpace E) : Prop :=
  ∃ (ι : Type u) (_ : Nonempty ι) (p : SeminormFamily ℂ E ι), @WithSeminorms ℂ E ι _ _ _ p t

variable [TopologicalSpace E]

/-- `E` is a Hausdorff locally convex topological vector space. -/
def IsHLCS : Prop := IsLocallyConvexTopology E ‹TopologicalSpace E› ∧ T2Space E

variable {E}

/-- A filter on `E` is Cauchy (for the additive uniform structure of `E`): it is proper and for
every `0`-neighbourhood `U` it contains a set `A` with `A - A ⊆ U`.  This is the filter form of the
Cauchy nets of Definition C.1.3.1(3). -/
def IsCauchyFilter (f : Filter E) : Prop :=
  f.NeBot ∧ ∀ U ∈ 𝓝 (0 : E), ∃ A ∈ f, ∀ x ∈ A, ∀ y ∈ A, x - y ∈ U

variable (E)

/-- `E` is complete (Definition C.1.3.1(4)): it is Hausdorff and every Cauchy filter (equivalently,
every Cauchy net) converges. -/
def IsCompleteTVS : Prop := T2Space E ∧ ∀ f : Filter E, IsCauchyFilter f → ∃ x : E, f ≤ 𝓝 x

/-- `E` is quasi-complete (§C.1.4): every bounded Cauchy filter converges; equivalently, every
closed bounded subset of `E` is complete. -/
def IsQuasiComplete : Prop :=
  T2Space E ∧ ∀ f : Filter E, IsCauchyFilter f → (∃ B ∈ f, Bornology.IsVonNBounded ℂ B) →
    ∃ x : E, f ≤ 𝓝 x

/-- `E` is a Fréchet space (Definition C.1.3.1(5)): locally convex, complete and metrizable. -/
def IsFrechet : Prop :=
  IsLocallyConvexTopology E ‹TopologicalSpace E› ∧ IsCompleteTVS E ∧
    TopologicalSpace.MetrizableSpace E

/-- `E` is bornological: every seminorm on `E` that is bounded on the bounded subsets of `E` is
continuous. -/
def IsBornological : Prop :=
  ∀ p : Seminorm ℂ E, (∀ B : Set E, Bornology.IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p

/-- `E` carries the finest locally convex topology. -/
def HasFinestLocallyConvexTopology : Prop :=
  ‹TopologicalSpace E› = sInf {t | IsLocallyConvexTopology E t}

/-- The strong topology `β(E, E')` on `E`: the topology of uniform convergence on the bounded
subsets of the strong dual `E'_β`, i.e. the topology induced on `E` by the canonical map
`E → (E'_β)'_β`. -/
def strongBidualTopology : TopologicalSpace E :=
  TopologicalSpace.induced
    (fun x : E => UniformOnFun.ofFun {B : Set (StrongDual ℂ E) | Bornology.IsVonNBounded ℂ B}
      (fun f : StrongDual ℂ E => f x))
    inferInstance

/-- `E` is reflexive (Example C.1.4.6(3)): the canonical double-duality map `E → (E'_β)'_β` is a
topological isomorphism.  Here: every continuous linear functional on the strong dual `E'_β` is
the evaluation at a unique point of `E`, and the topology of `E` is the one induced from the
strong bidual. -/
def IsReflexive : Prop :=
  (∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! x : E, ∀ f : StrongDual ℂ E, φ f = f x) ∧
    ‹TopologicalSpace E› = strongBidualTopology E

/-- `E` is a Montel space (Example C.1.4.6(3)): a Hausdorff locally convex space in which every
closed bounded subset is compact and which is reflexive. -/
def IsMontel : Prop :=
  IsHLCS E ∧ (∀ B : Set E, IsClosed B → Bornology.IsVonNBounded ℂ B → IsCompact B) ∧ IsReflexive E

end basic

section tensor

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable (F : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- The projective (`π`) topology on `E ⊗ F`: the finest locally convex topology for which the
canonical bilinear map `E × F → E ⊗ F` is continuous. -/
def projTensorTopology : TopologicalSpace (E ⊗[ℂ] F) :=
  sInf {t | IsLocallyConvexTopology (E ⊗[ℂ] F) t ∧
    @Continuous (E × F) (E ⊗[ℂ] F) _ t (fun p => p.1 ⊗ₜ[ℂ] p.2)}

/-- The inductive (`ι`) topology on `E ⊗ F`: the finest locally convex topology for which the
canonical bilinear map `E × F → E ⊗ F` is separately continuous. -/
def indTensorTopology : TopologicalSpace (E ⊗[ℂ] F) :=
  sInf {t | IsLocallyConvexTopology (E ⊗[ℂ] F) t ∧
    (∀ x : E, @Continuous F (E ⊗[ℂ] F) _ t (fun y => x ⊗ₜ[ℂ] y)) ∧
    (∀ y : F, @Continuous E (E ⊗[ℂ] F) _ t (fun x => x ⊗ₜ[ℂ] y))}

/-- The value `(x' ⊗ y')(u)` of the tensor product of two continuous linear functionals on a
tensor `u ∈ E ⊗ F`. -/
def tensorFunctional (ab : StrongDual ℂ E × StrongDual ℂ F) (u : E ⊗[ℂ] F) : ℂ :=
  TensorProduct.lid ℂ ℂ (TensorProduct.map (ab.1 : E →ₗ[ℂ] ℂ) (ab.2 : F →ₗ[ℂ] ℂ) u)

/-- The injective (`ε`) topology on `E ⊗ F`: the topology of uniform convergence on the products
`A × B` of an equicontinuous subset `A` of `E'` and an equicontinuous subset `B` of `F'`, where
`u ∈ E ⊗ F` is viewed as the function `(x', y') ↦ (x' ⊗ y')(u)` on `E' × F'`. -/
def epsTensorTopology : TopologicalSpace (E ⊗[ℂ] F) :=
  TopologicalSpace.induced
    (fun u : E ⊗[ℂ] F =>
      UniformOnFun.ofFun
        {S : Set (StrongDual ℂ E × StrongDual ℂ F) |
          ∃ (A : Set (StrongDual ℂ E)) (B : Set (StrongDual ℂ F)),
            Equicontinuous (fun a : A => (a : E → ℂ)) ∧
            Equicontinuous (fun b : B => (b : F → ℂ)) ∧ S = A ×ˢ B}
        (fun ab => tensorFunctional E F ab u))
    inferInstance

end tensor

section nuclear

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- `E` is nuclear (Definition C.2.4.1): `E` is a Hausdorff locally convex space and for every
Hausdorff locally convex space `F` the identity map `E ⊗_π F → E ⊗_ε F` is a linear topological
isomorphism, i.e. the projective and the injective topology on `E ⊗ F` coincide. -/
def IsNuclear : Prop :=
  IsHLCS E ∧ ∀ (F : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F], IsHLCS F →
    projTensorTopology E F = epsTensorTopology E F

/-- `E` is a strict LF-space (Example C.1.4.6(4), p. 664): `E` is the union of an increasing
sequence of subspaces `X n`, each of which is a Fréchet space for the topology induced from `E`,
and the topology of `E` is the locally convex inductive limit topology, i.e. the finest locally
convex topology for which all inclusions `X n → E` are continuous. -/
def IsStrictLF : Prop :=
  ∃ X : ℕ → Submodule ℂ E, Monotone X ∧ (∀ x : E, ∃ n, x ∈ X n) ∧ (∀ n, IsFrechet (X n)) ∧
    ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val}

/-- `E` is a strict countable locally convex inductive limit of nuclear Fréchet spaces
(Remark C.1.4.7): as `IsStrictLF`, with every step `X n` nuclear. -/
def IsStrictLFOfNuclearFrechet : Prop :=
  ∃ X : ℕ → Submodule ℂ E, Monotone X ∧ (∀ x : E, ∃ n, x ∈ X n) ∧
    (∀ n, IsFrechet (X n) ∧ IsNuclear (X n)) ∧
    ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val}

/-- `E` is an LF-space (Definition C.1.5.2): `E` is a Hausdorff locally convex space which is the
locally convex inductive limit of a sequence of Fréchet spaces with injective continuous
transition maps.  The steps are subspaces `X n` of `E`, each with its own Fréchet topology
`τ n`. -/
def IsLF : Prop :=
  IsHLCS E ∧ ∃ (X : ℕ → Submodule ℂ E) (τ : ∀ n, TopologicalSpace (X n)),
    (∀ x : E, ∃ n, x ∈ X n) ∧ (∀ n, @IsFrechet (X n) _ _ (τ n)) ∧
    (∀ n, ∃ h : X n ≤ X (n + 1),
      @Continuous (X n) (X (n + 1)) (τ n) (τ (n + 1)) (Submodule.inclusion h)) ∧
    ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E (τ n) t Subtype.val}

end nuclear

section maps

universe v

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- A linear map is a linear topological isomorphism: bijective, continuous, with continuous
inverse (i.e. open). -/
def IsLinearTopologicalIso (f : E →ₗ[ℂ] F) : Prop :=
  Function.Bijective f ∧ Continuous f ∧ IsOpenMap f

/-- A linear map is a linear topological embedding: injective and a homeomorphism onto its
image. -/
def IsLinearTopologicalEmbedding (f : E →ₗ[ℂ] F) : Prop := Topology.IsEmbedding f

/-- The bounded lifting property (Definition C.1.5.9): every bounded subset of `F` is contained in
the image of a bounded subset of `E`. -/
def LiftsBoundedSets (f : E → F) : Prop :=
  ∀ B : Set F, Bornology.IsVonNBounded ℂ B → ∃ B' : Set E, Bornology.IsVonNBounded ℂ B' ∧ B ⊆ f '' B'

end maps

end

end MasulloGRH


