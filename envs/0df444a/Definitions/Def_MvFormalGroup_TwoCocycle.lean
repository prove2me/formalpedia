-- Prove2me | Definitions.Def_MvFormalGroup_TwoCocycle
-- name    : MvFormalGroup_TwoCocycle
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/18d88f4d-ab55-5977-b38d-03f78a94b683
-- title:
--   Symmetric two-cocycles and additive coboundaries of formal group laws
-- statement:
--   Fix a commutative ring $R$ and an $n$-dimensional formal group law $F$ over $R$ in the sense of the project's [`MvFormalGroup`](../def/MvFormalGroup_BasicV2.html#L15) structure: an $n$-tuple `F.toPowerSeries` of power series in two blocks of variables indexed by `Fin n ⊕ Fin n`, with vanishing constant terms, the normalisation conditions on the linear coefficients in each block, and associativity as a field of the structure.
--
--   Two notions are introduced. First, [`MvFormalGroup.addCoboundary F g`](../def/MvFormalGroup_TwoCocycle.html#L14), for a power series $g$ in one block of $n$ variables, is the two-block series obtained as the substitution of the family `F.toPowerSeries` into $g$, minus the substitution of $X_{\mathrm{inl}\,l}$ for the $l$-th variable, minus the substitution of $X_{\mathrm{inr}\,l}$: in classical notation $\partial g(X,Y) = g(F(X,Y)) - g(X) - g(Y)$. No hypothesis on $g$ is imposed. Second, [`MvFormalGroup.IsSymmTwoCocycle F Γ`](../def/MvFormalGroup_TwoCocycle.html#L20) is a `Prop`-valued structure on a two-block series $\Gamma$ with three fields: the constant coefficient of $\Gamma$ vanishes; substituting $X_{\mathrm{inr}\,j}$ for the $j$-th left variable and $X_{\mathrm{inl}\,j}$ for the $j$-th right variable leaves $\Gamma$ unchanged, i.e. $\Gamma(Y,X) = \Gamma(X,Y)$; and, in the ring of power series in three blocks `Fin n ⊕ (Fin n ⊕ Fin n)` — the same ring in which the associativity axiom of $F$ is phrased — the identity $\Gamma(F(X,Y),Z) + \Gamma(X,Y) = \Gamma(X,F(Y,Z)) + \Gamma(Y,Z)$ holds, each term being an explicit substitution of the indicated families into $\Gamma$. Thus the predicate is a condition on the given series $\Gamma$ relative to the chosen presentation of $F$; it carries no further data and asserts nothing about module structures or about coboundaries being cocycles.
--
--   Two small results accompany the definitions: substituting an admissible family into the zero series yields zero, and consequently the zero series satisfies `IsSymmTwoCocycle` for every $F$.
--
--   **Relation to Mathlib.** Mathlib has no notion of multivariate formal group laws or of their symmetric two-cocycles; these are the project's own, phrased entirely in terms of Mathlib's multivariate power series substitution API (`subst`, `HasSubst`, `hasSubst_of_constantCoeff_zero`, `constantCoeff_subst_eq_zero`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_TwoCocycle.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {n : ℕ} {R : Type*} [CommRing R]

def addCoboundary (F : MvFormalGroup n R) (g : MvPowerSeries (Fin n) R) :
    MvPowerSeries (Fin n ⊕ Fin n) R :=
  subst F.toPowerSeries g
    - subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) R)) g
    - subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) R)) g

structure IsSymmTwoCocycle (F : MvFormalGroup n R) (Γ : MvPowerSeries (Fin n ⊕ Fin n) R) : Prop where

  constantCoeff_eq_zero : Γ.constantCoeff = 0

  symm :
    subst
      (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) R))
        fun j => X (Sum.inl j))
      Γ = Γ

  cocycle :
    subst
        (Sum.elim
          (fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
              fun l => X (Sum.inr (Sum.inl l)))
            (F.toPowerSeries j))
          fun j => X (Sum.inr (Sum.inr j)))
        Γ
      + subst
        (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
          fun l => X (Sum.inr (Sum.inl l)))
        Γ
      =
    subst
        (Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
          fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
              fun l => X (Sum.inr (Sum.inr l)))
            (F.toPowerSeries j))
        Γ
      + subst
        (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
          fun l => X (Sum.inr (Sum.inr l)))
        Γ

theorem subst_zero_of_hasSubst {σ τ : Type*} {a : σ → MvPowerSeries τ R} (ha : HasSubst a) :
    subst a (0 : MvPowerSeries σ R) = 0 := by
  rw [← coe_substAlgHom ha, map_zero]

theorem IsSymmTwoCocycle.zero (F : MvFormalGroup n R) : F.IsSymmTwoCocycle 0 where
  constantCoeff_eq_zero := map_zero _
  symm := subst_zero_of_hasSubst (hasSubst_of_constantCoeff_zero (by
      rintro (j | j) <;> exact constantCoeff_X _))
  cocycle := by
    have h1 : HasSubst (Sum.elim
        (fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
            fun l => X (Sum.inr (Sum.inl l)))
          (F.toPowerSeries j))
        fun j => X (Sum.inr (Sum.inr j))) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _))
          (by rintro (l | l) <;> exact constantCoeff_X _) (F.constantCoeff_eq_zero j)
      · exact constantCoeff_X _
    have h2 : HasSubst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
        fun l => X (Sum.inr (Sum.inl l))) :=
      hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _)
    have h3 : HasSubst (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
        fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
            fun l => X (Sum.inr (Sum.inr l)))
          (F.toPowerSeries j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_X _
      · exact constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _))
          (by rintro (l | l) <;> exact constantCoeff_X _) (F.constantCoeff_eq_zero j)
    have h4 : HasSubst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
        fun l => X (Sum.inr (Sum.inr l))) :=
      hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _)
    rw [subst_zero_of_hasSubst h1, subst_zero_of_hasSubst h2, subst_zero_of_hasSubst h3,
      subst_zero_of_hasSubst h4]

end MvFormalGroup

end


