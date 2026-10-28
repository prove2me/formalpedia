-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPndIdem
-- name    : IntMul_Kappa_R8_Data_BitOppbankPndIdem
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:01:34.652639+00:00
-- url     : https://prove2.me/theorems/631e8adc-f127-4355-8262-73e86e5bd7dc
-- title:
--   R8 Oppbank Pnd/prjM/Pc idempotence (densified)
-- statement:
--   Densified node projectors are idempotent: for every complemented subspace $V$, the $B$-orthogonal projector $\mathrm{prjM}(V)$ satisfies $\mathrm{prjM}(V)^2=\mathrm{prjM}(V)$; hence $\mathrm{Pnd}(\mathrm{sup})^2=\mathrm{Pnd}(\mathrm{sup})$ for every support, and $\mathrm{Pc}(1773+n)^2=\mathrm{Pc}(1773+n)$ whenever densified support $n$ is centred. Together with MoveFacts $\mathrm{Pc}$-idempotence on LOW/HIGH/PT codes, every code projector used by densified $\mathrm{Pis0}$ is idempotent under $\mathrm{HasCentre}$ hypotheses — unblocking full $h\mathrm{Pis0}$ toward $\mathrm{FB0\_ex}$.
-- source:
--   Mathlib Submodule.isIdempotentElem_projection; BitOppbankPnd prjM; MoveFacts Pc_idem_PT.

-- Densified Pnd/prjM idempotence (unblocks full hPis0 / FB0_ex).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# `prjM` / `Pnd` / densified `Pc` idempotence

Uses Mathlib `Submodule.isIdempotentElem_projection` + `LinearMap.toMatrix'_comp`.
Together with MoveFacts `Pc_idem_PT` this gives `Pc` idempotent on all code branches
when ND supports are centred — the missing half of `hPis0` for full `FB0_ex`.
-/

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts

namespace IntMul.Kappa.R8.Bit.Oppbank.PndIdem

theorem prjM_idem (V : Submodule ℚ V23) (h : IsCompl V (Bf.orthogonal V)) :
    prjM V h * prjM V h = prjM V h := by
  simp only [prjM]
  rw [← LinearMap.toMatrix'_comp]
  congr 1
  exact Submodule.isIdempotentElem_projection h

theorem Pnd_idem {sup : ℕ} (h : HasCentre sup) :
    Pnd sup * Pnd sup = Pnd sup := by
  rw [Pnd_eq_prj h]
  exact prjM_idem _ (compl_spanS h)

theorem Pnd_idem_zero {sup : ℕ} (h : ¬ HasCentre sup) :
    Pnd sup * Pnd sup = Pnd sup := by
  rw [Pnd_zero_of_no_centre h, Matrix.zero_mul]

theorem Pnd_idem_all {sup : ℕ} : Pnd sup * Pnd sup = Pnd sup := by
  by_cases h : HasCentre sup
  · exact Pnd_idem h
  · exact Pnd_idem_zero h

theorem PndD_idem (n : ℕ) : PndD n * PndD n = PndD n :=
  Pnd_idem_all

theorem Pc_idem_ND {n : ℕ} (hn : 1773 + n < codeBound)
    (hC : HasCentre (densSupG n)) :
    Pc (1773 + n) * Pc (1773 + n) = Pc (1773 + n) := by
  rw [Pc_of_ND n hn, PndD, Pnd_idem hC]

/-- Package: every densified ND code is idempotent under `HasCentre`. -/
theorem Pc_idem_dens {c : ℕ} (hc : c < codeBound)
    (hND : 1773 ≤ c → HasCentre (densSupG (c - 1773))) :
    Pc c * Pc c = Pc c := by
  by_cases h0 : c = 0
  · subst h0; exact Pc_idem_low
  by_cases h1 : c = 1
  · subst h1; exact Pc_idem_high
  by_cases hPT : c < 1773
  · have h2 : 2 ≤ c := by omega
    exact Pc_idem_PT h2 hPT
  · have hn : 1773 + (c - 1773) < codeBound := by omega
    have hC : HasCentre (densSupG (c - 1773)) := hND (by omega)
    have : c = 1773 + (c - 1773) := by omega
    rw [this]; exact Pc_idem_ND hn hC

theorem PndIdemStmt_holds : PndIdemStmt := fun {_} h => Pnd_idem h

end IntMul.Kappa.R8.Bit.Oppbank.PndIdem


