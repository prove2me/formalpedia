-- Prove2me | Definitions.Def_PreservePast_DetAchieves
-- name    : PreservePast_DetAchieves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:41:30.365692+00:00
-- url     : https://prove2.me/theorems/e00a6de3-c591-4277-a512-4c9e53e1e040
-- title:
--   Deterministic $B$-bit code achieving the protective update with certainty
-- statement:
--   A **deterministic $B$-bit code** is a pair of functions: an encoder $\mathrm{enc}(h)\in\{0,\dots,2^B-1\}$ of the history and a decoder $\mathrm{dec}(M,x,p)\in\mathbb R^{m\times n}$ of the message and the query. It **achieves** the task with parameters $(r,\epsilon,\xi,R)$ when, for every history $h$ and every promised query $(x,p)$, the update $\mathrm{dec}(\mathrm{enc}(h),x,p)$ is successful.
--
--   This is the form of the paper's upper bounds: Theorem 9's code and the code behind the upper half of Theorem 4 are deterministic and support every promised query. A deterministic code is a randomized protocol on a one-point coin space.
--
--   **Formalization Note** No measurability is imposed (there are no coins).
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8), remark after Theorem 4; §C.1, p.17, Theorem 9

import Mathlib
import Definitions.Def_PreservePast_IsPromised
import Definitions.Def_PreservePast_IsSuccess

open Matrix

namespace PreservePast

/-- **A deterministic B-bit code that achieves the protective-update task with certainty.**
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8), after Theorem 4: "The upper bound is deterministic: for every fixed
history and every promised unit query (x, p), it returns Hx = p, rank H ≤ r, ‖H‖_F ≤ √3, and
f(H) ≤ ϵ"; §C.1, p.17, Theorem 9: "The code is deterministic and supports every promised query."

The encoder `enc h ∈ {0, …, 2^B − 1}` reads only the history; the decoder `dec M x p` reads only
the message and the query. `DetAchieves enc dec r ε ξ R` holds when for every history `h` and every
promised query `(x, p)` (13) the decoded update is successful (14).

**Formalization Note.** No coins and no measurability: a deterministic code is an arbitrary pair of
functions. It is the special case of a randomized protocol on a one-point coin space. -/
def DetAchieves {m n K B : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ}
    (enc : (Fin K → Task W₀) → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ)
    (r : ℕ) (ε ξ R : ℝ) : Prop :=
  ∀ h x p, IsPromised r R h x p → IsSuccess r R ξ ε h x p (dec (enc h) x p)

end PreservePast


