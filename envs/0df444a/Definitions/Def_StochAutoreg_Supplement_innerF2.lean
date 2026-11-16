-- Prove2me | Definitions.Def_StochAutoreg_Supplement_innerF2
-- name    : StochAutoreg_Supplement_innerF2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:18:51.797931+00:00
-- url     : https://prove2.me/theorems/d4ed2190-62bb-4eb7-86ac-3a5b131c04bf
-- title:
--   Parity $\langle a,u\rangle_{\mathbb F_2}$ of two bit vectors
-- statement:
--   For $a,u\in\{0,1\}^m$,
--
--   $$\langle a,u\rangle_{\mathbb F_2}=\Bigl(\sum_{i=1}^m a_iu_i\Bigr)\bmod 2 .$$
--
--   The map $u\mapsto\langle a,u\rangle_{\mathbb F_2}$ is the noiseless parity with secret $a$ of the LPN assumption.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, LPN assumption, p.23

import Mathlib

namespace StochAutoreg

namespace Supplement

/-- The **parity** `⟨a, u⟩_{F₂} = (∑_{i=1}^m a_i u_i) mod 2` of two bit vectors, as a bit.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, LPN assumption,
p.23. -/
def innerF2 {m : ℕ} (a u : Fin m → Bool) : Bool :=
  (Finset.univ.filter fun i => a i && u i).card % 2 == 1

end Supplement

end StochAutoreg


