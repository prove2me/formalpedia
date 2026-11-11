-- Prove2me | Definitions.Def_PermInvCC_J
-- name    : PermInvCC_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:03.154825+00:00
-- url     : https://prove2.me/theorems/264f89d3-229a-4a9a-a136-60e9be595bd9
-- title:
--   Auxiliary distributions $J_W$ and $J^E_T$
-- statement:
--   Let $W=(W_e)_e$ be nonnegative with total $w=\sum_eW_e$. For $w>0$, $J_W$ samples independently an exponential waiting time of rate $w$ and a label $e$ with probability $W_e/w$; its density on component $e$ is
--   $$W_e\,e^{-wz}\qquad(z>0).$$
--   For $w=0$, $J_W=\delta_\bot$. For a table $T$ and an event $E$, $J^E_T:=J_{(T_e)_{e\in E}}$.
--
--   Their Hellinger distances equal the cut separations (Lemma 2.6); they are used only in the analysis.
--
--   **Formalization Note** Nonnegativity of $W$ is an argument of the definition.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), p.10

import Mathlib
import Definitions.Def_PermInvCC_DensDist

namespace PermInvCC

/-- The auxiliary distribution **`J_W`** of a nonnegative weight vector `W = (W_e)_{e}` with total
`w = ∑_e W_e` (Y. Huang and Z. Ye, arXiv:2609.40116, held version sha256 fe1797dd…, p.10): for
`w > 0`, sample independently an exponential waiting time of rate `w` and a label `e` with
probability `W_e / w`, giving density `W_e e^{−wz}` on component `e`; for `w = 0`, `J_W = δ_⊥`.

**Formalization Note.** The nonnegativity of `W` is an argument `hW`. For `w = 0` the mass at `⊥`
is `1` and all densities vanish; for `w > 0` the mass at `⊥` is `0`. -/
noncomputable def J {ι : Type} [Fintype ι] (W : ι → ℝ) (hW : ∀ e, 0 ≤ W e) : DensDist ι where
  pbot := if ∑ e, W e = 0 then 1 else 0
  dens e z := if ∑ e, W e = 0 then 0 else W e * Real.exp (-(∑ e, W e) * z)
  pbot_nonneg := by split_ifs <;> norm_num
  dens_nonneg e z := by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hW e) (Real.exp_pos _).le
  dens_integrable e := by
    split_ifs with h
    · exact MeasureTheory.integrableOn_zero
    · have hpos : 0 < ∑ e, W e :=
        lt_of_le_of_ne (Finset.sum_nonneg fun e _ => hW e) (Ne.symm h)
      exact (exp_neg_integrableOn_Ioi 0 hpos).const_mul (W e)

/-- `J^E_T := J_{(T_e)_{e∈E}}` for a table `T` and a set of cells `E` (arXiv:2609.40116, held
version sha256 fe1797dd…, p.10). -/
noncomputable def JE {q : ℕ} (E : Finset (Fin q × Fin q)) (T : Fin q → Fin q → ℕ) : DensDist E :=
  J (fun e : E => (T e.1.1 e.1.2 : ℝ)) (fun _ => Nat.cast_nonneg _)

end PermInvCC


