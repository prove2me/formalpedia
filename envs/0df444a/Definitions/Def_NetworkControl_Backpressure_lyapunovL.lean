-- Prove2me | Definitions.Def_NetworkControl_Backpressure_lyapunovL
-- name    : NetworkControl_Backpressure_lyapunovL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:21:31.243607+00:00
-- url     : https://prove2.me/theorems/19131296-2e1f-44b9-846c-21b56e4ce96f
-- title:
--   Quadratic Lyapunov function L(U(t)) = Σ U_i(t)^2, p. 49
-- statement:
--   $L(U(t)):=\sum_{i=1}^L U_i(t)^2$, the quadratic Lyapunov function of a vector queue
--   backlog, defined just above Lemma 4.1 (p. 49, unnumbered display, §4.4).
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, p. 49, unnumbered display equation, §4.4

import Mathlib

namespace NetworkControl.Backpressure

/-- `L(U(t)) := Σ_{i=1}^L U_i(t)^2`, the quadratic Lyapunov function of a vector queue
backlog, defined just above Lemma 4.1 (p. 49, unnumbered display, §4.4). -/
noncomputable def lyapunovL {L : ℕ} (u : Fin L → ℝ) : ℝ :=
  ∑ i : Fin L, (u i) ^ 2

end NetworkControl.Backpressure


