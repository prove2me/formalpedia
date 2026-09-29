-- Prove2me | Definitions.Def_MazurAdmissible_GaloisModule
-- name    : MazurAdmissible_GaloisModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/7d839e6a-5cf1-5f3f-a60b-7a36f75fe93b
-- title:
--   Mazur-admissible Galois modules and finite flat models over ℤ
-- statement:
--   Fix an additive commutative group $M$. An `OpenAction M` is a structure bundling a group homomorphism $\varphi\colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{Aut}(M)$ (automorphisms of the additive group, with $\overline{\mathbb{Q}}$ realised as `AlgebraicClosure ℚ`) together with a proof, carried as a field of the structure, that $\ker\varphi$ is open for the Krull topology; so the action factors through a finite quotient. All later notions take such a $\Phi$, never a bare homomorphism.
--
--   For additive subgroups $A, B \le M$, `IsTrivialStep Φ A B` asserts $\varphi(\sigma)x - x \in A$ for every $\sigma$ and every $x \in B$, and `IsCyclotomicStep p Φ A B` asserts that for every $\sigma$, every $\zeta \in \overline{\mathbb{Q}}$ that is a primitive $p$-th root of unity, every natural number $a$ with $\sigma\zeta = \zeta^{a}$, and every $x \in B$, one has $\varphi(\sigma)x - a\cdot x \in A$ ($a\cdot x$ being the $\mathbb{N}$-multiple). These are congruences modulo $A$, not statements about an isomorphism of $B/A$.
--
--   An `AdmissibleChain p Φ` is a structure consisting of a length $n$, a family `step : Fin (n+1) → AddSubgroup M` with `step 0 = ⊥` and `step (Fin.last n) = ⊤`, inclusions between consecutive terms, a Boolean `tag` on the $n$ steps, a proof that each quotient `step i.succ / step i.castSucc` has cardinality exactly $p$, and a proof that the $i$-th step is a trivial step when `tag i` is true and a cyclotomic step otherwise. `filtLength` returns $n$, `filtAlpha` the number of steps tagged true, and `IsMazurAdmissible p Φ` is the nonemptiness of the type of such chains.
--
--   Separately, `ptMul` defines, for a commutative semiring $G$ with a $\mathbb{Z}$-Hopf-algebra structure, the convolution of two $\mathbb{Z}$-algebra maps $a, b\colon G \to \overline{\mathbb{Q}}$ as the comultiplication $G \to G \otimes_{\mathbb{Z}} G$ followed by the lift of the pair $(a,b)$. Then `HasFiniteFlatModelOverInt Φ` asserts the existence of such a $G$, cocommutative and flat and finite as a $\mathbb{Z}$-module, and of a bijection $f$ from the set of $\mathbb{Z}$-algebra maps $G \to \overline{\mathbb{Q}}$ onto $M$ carrying `ptMul` to addition and commuting with the Galois actions, where $\sigma$ acts on points by post-composition with $\sigma$ viewed as a $\mathbb{Z}$-algebra endomorphism of $\overline{\mathbb{Q}}$.
--
--   **Relation to Mathlib.** Mathlib has no notion of admissible $p$-group scheme or of an admissible Galois module; these are the project's own definitions, built on Mathlib's Krull topology, `AddAut`, `HopfAlgebra` with `Bialgebra.comulAlgHom`, and `Module.Flat`/`Module.Finite`. The Galois action is recorded as a homomorphism into `AddAut M` with open kernel rather than through a Mathlib continuous-action or representation typeclass.
--
--   **Where it is used.** These definitions give the Galois-module formulation of Mazur's admissible $p$-group schemes over $\operatorname{Spec}\mathbb{Z}$: a module is Mazur-admissible when it admits a filtration whose successive quotients have order $p$ and on which the Galois group acts either trivially or through the mod-$p$ cyclotomic character, and `HasFiniteFlatModelOverInt` records the existence of a finite flat commutative group scheme over $\mathbb{Z}$ whose $\overline{\mathbb{Q}}$-points realise the module. They are the vocabulary in which the $p$-torsion of the Frey curve and its local behaviour are described in the irreducibility and level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MazurAdmissible_GaloisModule.lean

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace MazurAdmissible

universe u

local notation "Qbar" => AlgebraicClosure ℚ

structure OpenAction (M : Type u) [AddCommGroup M] where

  φ : (Qbar ≃ₐ[ℚ] Qbar) →* AddAut M

  hker : IsOpen (φ.ker : Set (Qbar ≃ₐ[ℚ] Qbar))

variable {M : Type u} [AddCommGroup M]

def IsTrivialStep (Φ : OpenAction M) (A B : AddSubgroup M) : Prop :=
  ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ x ∈ B, Φ.φ σ x - x ∈ A

def IsCyclotomicStep (p : ℕ) (Φ : OpenAction M) (A B : AddSubgroup M) : Prop :=
  ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ ζ : Qbar, IsPrimitiveRoot ζ p → ∀ a : ℕ, σ ζ = ζ ^ a →
    ∀ x ∈ B, Φ.φ σ x - a • x ∈ A

structure AdmissibleChain (p : ℕ) (Φ : OpenAction M) where

  n : ℕ

  step : Fin (n + 1) → AddSubgroup M

  hbot : step 0 = ⊥

  htop : step (Fin.last n) = ⊤

  hmono : ∀ i : Fin n, step i.castSucc ≤ step i.succ

  tag : Fin n → Bool

  hcard : ∀ i : Fin n,
    Nat.card (↥(step i.succ) ⧸ (step i.castSucc).addSubgroupOf (step i.succ)) = p

  hact : ∀ i : Fin n,
    if tag i then IsTrivialStep Φ (step i.castSucc) (step i.succ)
      else IsCyclotomicStep p Φ (step i.castSucc) (step i.succ)

def filtAlpha {p : ℕ} {Φ : OpenAction M} (c : AdmissibleChain p Φ) : ℕ :=
  (Finset.univ.filter fun i => c.tag i = true).card

def filtLength {p : ℕ} {Φ : OpenAction M} (c : AdmissibleChain p Φ) : ℕ := c.n

def IsMazurAdmissible (p : ℕ) (Φ : OpenAction M) : Prop :=
  Nonempty (AdmissibleChain p Φ)

def ptMul {G : Type*} [CommSemiring G] [HopfAlgebra ℤ G] (a b : G →ₐ[ℤ] Qbar) : G →ₐ[ℤ] Qbar :=
  (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom ℤ G)

def HasFiniteFlatModelOverInt (Φ : OpenAction M) : Prop :=
  ∃ (G : Type) (_ : CommSemiring G) (_ : HopfAlgebra ℤ G) (_ : Coalgebra.IsCocomm ℤ G)
    (_ : Module.Flat ℤ G) (_ : Module.Finite ℤ G)
    (f : (G →ₐ[ℤ] Qbar) → M),
    Function.Bijective f ∧
    (∀ a b, f (ptMul a b) = f a + f b) ∧
    (∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ a,
      f ((σ : Qbar →+* Qbar).toIntAlgHom.comp a) = Φ.φ σ (f a))

end MazurAdmissible


