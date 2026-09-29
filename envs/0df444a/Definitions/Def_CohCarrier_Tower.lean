-- Prove2me | Definitions.Def_CohCarrier_Tower
-- name    : CohCarrier_Tower
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/818c0cd5-22ac-5454-a7f0-8cc7ca5c4742
-- title:
--   Hecke operator as R[X]-action on cohomology carriers
-- statement:
--   Throughout, $R$ is a commutative ring, $A$ (and $B$) are $R$-modules, $M$ is a level, $H \le (\mathbb{Z}/M)^\times$ a subgroup, and the carrier is $H^1(M,H;A) = \mathrm{Hom}(\Gamma_H(M), A)$, the group of additive homomorphisms from the additivisation of $\Gamma_H(M)$ to $A$, with its pointwise $R$-module structure. For $\ell$ with $\ell \neq 0$, `heckeTLin` records the operator `heckeT` — restriction of $\varphi$ along the homomorphism `conjL`, which sends $\gamma \in \Gamma_H(M) \cap \Gamma^0(\ell)$, written $\begin{pmatrix} a & b \\ c & d\end{pmatrix}$, to $\begin{pmatrix} a & b/\ell \\ c\ell & d\end{pmatrix}$, followed by the additive transfer (corestriction) from the finite-index subgroup back to $\Gamma_H(M)$ — as an $R$-linear endomorphism; `heckeTLin_apply` states that the two agree pointwise. `Car R A M H ℓ₀` is then the same group viewed through Mathlib's `Module.AEval'` as a module over $R[X]$ in which $X$ acts by this operator.
--
--   `legOfComm` takes an $R$-linear map $f : H^1(M,H;A) \to H^1(M',H';B)$ together with the hypothesis that $f$ commutes with the two operators at the same index $\ell_0$, i.e. $f(T_{\ell_0}\varphi) = T_{\ell_0}(f\varphi)$ for all $\varphi$, and yields the induced $R[X]$-linear map between the corresponding carriers; `legOfComm_of` is its defining equation on the canonical images of elements. Next, `tw R ℓ₀` is the polynomial $X - (\ell_0 + 1)$ of $R[X]$; `tw_smul_of` identifies its action on the image of $F$ with the image of $T_{\ell_0}F - (\ell_0+1)\cdot F$, the predicate `IsEis R A M H ℓ₀ F` is exactly the equation $T_{\ell_0}F = (\ell_0+1)\cdot F$, and `tw_smul_of_eq_zero` says that $X-(\ell_0+1)$ annihilates such $F$.
--
--   A final section is pure linear algebra over $R$: for $r_L, d : V \to L$ and $i, j : L \to L_2$, `threeCopy` is the map $(f_1,f_2,f_3) \mapsto i(r_L f_1) + (j(r_L f_2) + j(d f_3))$ on $V \times V \times V$; `embComb q T` is $v \mapsto (q\cdot v, -Tv, v)$, which is injective because of its last coordinate; and `threeCopy_embComb_apply` computes the composite as $q\cdot i(r_L v) - j(r_L(Tv)) + j(dv)$.
--
--   **Relation to Mathlib.** The $R[X]$-module structure is Mathlib's `Module.AEval'` with the induced map produced by `LinearMap.ofAEval`, so no new algebraic structure is introduced here; the underlying carrier `H1` and the Hecke operator `heckeT`, built from Mathlib's congruence subgroups and group-theoretic transfer, are the project's own.
--
--   **Where it is used.** These carriers provide the Hecke modules of weight-two level-$\Gamma_H(M)$ cohomology on which the level-raising and level-lowering comparisons are run: the $R[X]$-structure lets one pass to the non-Eisenstein part by inverting or localising at $X-(\ell_0+1)$, and `legOfComm` transports classes along degeneracy maps, further Hecke and diamond operators, and coefficient changes. The three-copy map and the embedding `embComb` are the linear-algebra shape of the level-raising map along pairs of degeneracy legs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CohCarrier_Tower.lean

import Definitions.Def_CohCarrier_Level
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CohCarrier

open Polynomial

section Linear

variable (R : Type*) [CommRing R] (A : Type*) [AddCommGroup A] [Module R A]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

noncomputable def heckeTLin (ℓ : ℕ) [NeZero ℓ] : H1 M H A →ₗ[R] H1 M H A where
  toFun φ := coresAdd _ (φ.comp (MonoidHom.toAdditive (conjL M H ℓ)))
  map_add' φ ψ := by
    have : (φ + ψ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) + ψ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by
      ext; rfl
    rw [this, coresAdd_add]
  map_smul' r φ := by
    have : (r • φ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        r • φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by ext; rfl
    rw [this, coresAdd_smul]
    rfl

theorem heckeTLin_apply (ℓ : ℕ) [NeZero ℓ] (φ : H1 M H A) :
    heckeTLin R A M H ℓ φ = heckeT M H ℓ A φ := rfl

abbrev Car (ℓ₀ : ℕ) [NeZero ℓ₀] : Type _ := Module.AEval' (heckeTLin R A M H ℓ₀)

end Linear

section Leg

variable (R : Type*) [CommRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] {B : Type*} [AddCommGroup B] [Module R B]
variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {M' : ℕ} {H' : Subgroup (ZMod M')ˣ}

noncomputable def legOfComm (ℓ₀ : ℕ) [NeZero ℓ₀] (f : H1 M H A →ₗ[R] H1 M' H' B)
    (hf : ∀ φ, f (heckeT M H ℓ₀ A φ) = heckeT M' H' ℓ₀ B (f φ)) :
    Car R A M H ℓ₀ →ₗ[R[X]] Car R B M' H' ℓ₀ :=
  LinearMap.ofAEval (heckeTLin R A M H ℓ₀)
    ((Module.AEval'.of (heckeTLin R B M' H' ℓ₀)).toLinearMap ∘ₗ f) (fun φ => by
      show Module.AEval'.of (heckeTLin R B M' H' ℓ₀) (f (heckeT M H ℓ₀ A φ))
        = (X : R[X]) • Module.AEval'.of (heckeTLin R B M' H' ℓ₀) (f φ)
      rw [hf, Module.AEval'.X_smul_of]
      rfl)

theorem legOfComm_of (ℓ₀ : ℕ) [NeZero ℓ₀] (f : H1 M H A →ₗ[R] H1 M' H' B)
    (hf : ∀ φ, f (heckeT M H ℓ₀ A φ) = heckeT M' H' ℓ₀ B (f φ)) (φ : H1 M H A) :
    legOfComm R ℓ₀ f hf (Module.AEval'.of (heckeTLin R A M H ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R B M' H' ℓ₀) (f φ) := by
  simp [legOfComm, LinearMap.ofAEval]

end Leg

section Eisenstein

variable (R : Type*) [CommRing R] (A : Type*) [AddCommGroup A] [Module R A]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

noncomputable abbrev tw (ℓ₀ : ℕ) : R[X] := (X : R[X]) - C ((ℓ₀ : R) + 1)

set_option backward.isDefEq.respectTransparency false in

theorem tw_smul_of (ℓ₀ : ℕ) [NeZero ℓ₀] (F : H1 M H A) :
    tw R ℓ₀ • Module.AEval'.of (heckeTLin R A M H ℓ₀) F
      = Module.AEval'.of (heckeTLin R A M H ℓ₀) (heckeT M H ℓ₀ A F - ((ℓ₀ : R) + 1) • F) := by
  rw [sub_smul, Module.AEval'.X_smul_of, map_sub, LinearEquiv.map_smul, Polynomial.C_eq_algebraMap,
    algebraMap_smul]
  rfl

def IsEis (ℓ₀ : ℕ) [NeZero ℓ₀] (F : H1 M H A) : Prop :=
  heckeT M H ℓ₀ A F = ((ℓ₀ : R) + 1) • F

set_option backward.isDefEq.respectTransparency false in

theorem tw_smul_of_eq_zero (ℓ₀ : ℕ) [NeZero ℓ₀] (F : H1 M H A) (hF : IsEis R A M H ℓ₀ F) :
    tw R ℓ₀ • Module.AEval'.of (heckeTLin R A M H ℓ₀) F = 0 := by
  rw [tw_smul_of, hF, sub_self, map_zero]

end Eisenstein

section ThreeCopy

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {L : Type*} [AddCommGroup L] [Module R L]
variable {L2 : Type*} [AddCommGroup L2] [Module R L2]

def threeCopy (rL d : V →ₗ[R] L) (i j : L →ₗ[R] L2) : (V × V × V) →ₗ[R] L2 :=
  (i ∘ₗ rL) ∘ₗ LinearMap.fst R V (V × V) +
    ((j ∘ₗ rL) ∘ₗ LinearMap.fst R V V + (j ∘ₗ d) ∘ₗ LinearMap.snd R V V) ∘ₗ LinearMap.snd R V (V × V)

theorem threeCopy_apply (rL d : V →ₗ[R] L) (i j : L →ₗ[R] L2) (f : V × V × V) :
    threeCopy rL d i j f = i (rL f.1) + (j (rL f.2.1) + j (d f.2.2)) := by
  simp [threeCopy]

def embComb (q : R) (T : V →ₗ[R] V) : V →ₗ[R] V × V × V :=
  (q • LinearMap.id).prod ((-T).prod LinearMap.id)

theorem embComb_apply (q : R) (T : V →ₗ[R] V) (v : V) :
    embComb q T v = (q • v, -T v, v) := rfl

theorem embComb_injective (q : R) (T : V →ₗ[R] V) : Function.Injective (embComb q T) :=
  fun v v' h => by simpa [embComb] using congrArg (fun w : V × V × V => w.2.2) h

theorem threeCopy_embComb_apply (rL d : V →ₗ[R] L) (i j : L →ₗ[R] L2) (q : R) (T : V →ₗ[R] V)
    (v : V) :
    threeCopy rL d i j (embComb q T v) = q • i (rL v) - j (rL (T v)) + j (d v) := by
  rw [embComb_apply, threeCopy_apply, map_smul, map_smul, map_neg, map_neg]
  abel

end ThreeCopy

end CohCarrier


