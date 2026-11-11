-- Prove2me | Definitions.Def_StabTestMem_hsProb
-- name    : StabTestMem_hsProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:27.091513+00:00
-- url     : https://prove2.me/theorems/196dfade-bfbc-4140-9ff7-b39ef794c832
-- title:
--   Output distribution $P^\beta_{a,r}$ of Algorithm 3
-- statement:
--   The output distribution of Algorithm 3 on one copy of $|\psi\rangle$ is
--
--   $$P^\beta_{a,r}(s,b)=\big\|K^\beta_{s,b}|\psi\rangle\big\|^2,\qquad (s,b)\in\mathbb F_2^m\times\mathbb F_2 .$$
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 4.5, p. 30; p. 31

import Definitions.Def_StabTestMem_hsKraus

namespace StabTestMem

open QAlgorithms

/-- **Output distribution `P^β_{a,r}` of Algorithm 3 on one copy.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 4.5, p. 30, and
p. 31: "Hence P^β_{a,r}(s, b) = ‖K^β_{s,b} |ψ⟩‖^2."

`hsProb ψ a r β (s, b) = ‖K^β_{s,b} ψ‖²` with `K^β_{s,b}` = `hsKraus a r β s b`. -/
noncomputable def hsProb {k m : ℕ} (ψ : EuclideanSpace ℂ (Qubits (k + m))) (a : CutRankSched.Pauli k)
    (r : Fin m → ZMod 2) (β : ZMod 2) (w : (Fin m → ZMod 2) × ZMod 2) : ℝ :=
  ‖act (hsKraus a r β w.1 w.2) ψ‖ ^ 2

end StabTestMem


