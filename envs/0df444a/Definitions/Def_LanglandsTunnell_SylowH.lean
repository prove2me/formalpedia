-- Prove2me | Definitions.Def_LanglandsTunnell_SylowH
-- name    : LanglandsTunnell_SylowH
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/ebcbebaf-3452-5b4b-ab3b-a35523477856
-- title:
--   Sylow 2-subgroup of a Galois group via explicit matrices
-- statement:
--   Throughout, $L$ is a number field and $e$ is a multiplicative isomorphism from the group $L \simeq_{\mathbb{Q}} L$ of $\mathbb{Q}$-algebra automorphisms of $L$ onto $\mathrm{GL}_2(\mathbb{Z}/3)$. Under these standing assumptions, `sylowH e` is the subgroup of $L \simeq_{\mathbb{Q}} L$ whose carrier consists of those $\gamma$ for which there is a matrix $M$ in the explicit list `P16` with $M$ reduced entrywise equal to the underlying $2 \times 2$ matrix of $e(\gamma)$. Here the reduction is the entrywise image under `red`, the ring homomorphism $\mathbb{Z}[\sqrt{-2}] \to \mathbb{Z}/3$ sending $\sqrt{-2}$ to $-1$, and `P16` is the sublist of the $48$-element list `K48` of matrices over $\mathbb{Z}[\sqrt{-2}]$ — the multiplicative closure of $\{$`Slift`$,$ `Tlift`$\}$ — consisting of those $g$ with $g\,T = t\,g$ for some $t \in \{T, T^3, T^5, T^7\}$, $T =$ `Tlift`; `P16` has $16$ entries, contains $1$ and `Tlift`, and does not contain `Slift`. So membership in `sylowH e` is a congruence condition on the matrix $e(\gamma)$ rather than a condition on a lift: $\gamma$ lies in the subgroup exactly when $e(\gamma)$ is congruent modulo $3$ to one of the sixteen chosen integral matrices.
--
--   That this carrier is a subgroup rests on the list facts that $1 \in$ `P16` and that `P16` is closed under multiplication, together with an auxiliary decidable check that for every $M \in$ `P16` one has $M \cdot M^{7} = M^{7} \cdot M = 1$ with $M^{7} \in$ `P16`, which supplies inverses. The companion lemma `mem_sylowH_iff` restates membership in `sylowH e` in exactly this form, for a given isomorphism $e$ and automorphism $\gamma$. No cardinality or index assertion about `sylowH e` is made here.
--
--   **Relation to Mathlib.** Built on Mathlib's `Subgroup`, `Zsqrtd` and `Matrix.GeneralLinearGroup`; the explicit integral matrix set and its reduction modulo $1+\sqrt{-2}$ are the project's own, Mathlib having no such presentation of $\mathrm{GL}_2(\mathbb{F}_3)$.
--
--   **Where it is used.** The subgroup arises in the Langlands–Tunnell input to the proof: for an octahedral field $L$ with $\mathrm{Gal}(L/\mathbb{Q}) \cong \mathrm{GL}_2(\mathbb{F}_3)$, a $2$-Sylow subgroup of index $3$ cuts out the cubic resolvent field over which the representation becomes dihedral, and hence automorphic by base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_SylowH.lean

import Definitions.Def_LanglandsTunnell_Lift48
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.NumberField.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace LanglandsTunnell

open FLT.ExplicitLift LanglandsTunnell.Lift48

private theorem P16_mul_pw_seven :
    ∀ x ∈ P16, x * pw x 7 = 1 ∧ pw x 7 * x = 1 ∧ pw x 7 ∈ P16 := by
  decide

variable {L : Type} [Field L] [NumberField L]

def sylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Subgroup (L ≃ₐ[ℚ] L) where
  carrier := {γ | ∃ M ∈ P16,
    M.map red = ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))}
  one_mem' := ⟨1, one_mem_P16.1, by rw [map_one, Units.val_one, Matrix.map_one _ (map_zero red) (map_one red)]⟩
  mul_mem' := by
    rintro a b ⟨M, hM, hMa⟩ ⟨N, hN, hNb⟩
    exact ⟨M * N, P16_mul_closed M hM N hN, by rw [Matrix.map_mul, hMa, hNb, map_mul, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨M, hM, hMa⟩
    refine ⟨pw M 7, (P16_mul_pw_seven M hM).2.2, ?_⟩
    rw [map_inv]
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    rw [← hMa, ← Matrix.map_mul, (P16_mul_pw_seven M hM).1, Matrix.map_one _ (map_zero red) (map_one red)]

theorem mem_sylowH_iff (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (γ : L ≃ₐ[ℚ] L) :
    γ ∈ sylowH e ↔ ∃ M ∈ P16,
      M.map red = ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  Iff.rfl

end LanglandsTunnell


