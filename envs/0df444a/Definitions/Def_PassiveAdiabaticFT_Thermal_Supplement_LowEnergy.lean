-- Prove2me | Definitions.Def_PassiveAdiabaticFT_Thermal_Supplement_LowEnergy
-- name    : PassiveAdiabaticFT_Thermal_Supplement_LowEnergy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:58:37.226766+00:00
-- url     : https://prove2.me/theorems/5efad043-2c1b-4ef7-908a-beab7ae3ed7c
-- title:
--   Acceptable syndromes below an inclusive energy threshold
-- statement:
--   Let $C$ be a stabilizer code on $n$ qubits with check generators indexed by $\{0,\ldots,m-1\}$. Write $\Omega$ for its acceptable syndromes, $|s|$ for the number of violated checks and $E[s]=2J|s|$ for the energy at penalty $J$. For a real threshold $E$, define
--
--   $$\Omega_{\le E}=\{s\in\Omega:2J|s|\le E\}.$$
--
--   This finite set includes the threshold endpoint and excludes inadmissible check strings. It supplies the denominator in the finite-size barrier-versus-rarity bound. The function is defined at every real threshold: it is empty for $E<0$ when $J>0$, and equals $\Omega$ when $E\ge 2Jm$ and $J>0$.
-- source:
--   Arsalan Motamedi, Peter Love, STOC 2027 submission #1144 (October 2026), p. 15, (2.15); Theorem 2.9, p. 17, (2.27).

import Definitions.Def_PassiveAdiabaticFT_Thermal_CodeBlock

set_option autoImplicit false

noncomputable section

namespace PassiveAdiabaticFT.Thermal.Supplement

open Classical in
/-- Equation (2.15), p. 15: the acceptable syndromes at energy at most E.
The endpoint is included; inadmissible binary check strings are excluded. -/
def omegaLe {n : ℕ} (C : StabCode n) (J E : ℝ) : Finset (Fin C.m → ZMod 2) :=
  C.Omega.filter fun s => C.energy J s ≤ E

end PassiveAdiabaticFT.Thermal.Supplement


