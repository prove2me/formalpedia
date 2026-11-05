-- Prove2me | Definitions.Def_KMSHolder_posPowGraph
-- name    : KMSHolder_posPowGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:40:10.809644+00:00
-- url     : https://prove2.me/theorems/4d7589b6-c5a3-4423-8f04-c5e4ec19df4e
-- title:
--   Graph of the power $T^z$ of a positive operator (support convention)
-- statement:
--   For a positive self-adjoint operator $T$ (given by its functional calculus) and $z \in \mathbb C$, the **graph of $T^z$** is the set of pairs $(x, y)$ with
--
--   $$
--   c_{N,z}(T)\, x \longrightarrow y \qquad (N \to \infty),
--   $$
--
--   where $c_{N,z}(u) = \min(1, Nu^+)\,(\max(1/N, \min(N,u)))^z$. For $\Re z \ge 0$ it is the graph of the closed operator $T^z$ with the support convention $T^z = 0$ on $\ker T$. With $T = \Delta_{\phi,\Omega}$ it gives the powers $\Delta^z_{\phi,\Omega}$ in Araki's estimate (8) and in Lemma 4.1.
--
--   **Formalization Note** The kernel convention is Araki–Masuda's for non-faithful $\phi$; for faithful $\phi$ the kernel is trivial and the convention is void.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, §3, pp.4–6; eq. (8), p.5; eq. (18), p.7

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_KMSHolder_PosSpectralCalculus
import Definitions.Def_KMSHolder_posCut

open OAI.BoundedRecovery
open Filter Topology

namespace KMSHolder

/-- The graph of `T^z` for a positive operator `T` (`PosSpectralCalculus`): `(x, y)` with
`posCut N z (T) x → y` as `N → ∞`.

**Formalization Note.** For `ℜz ≥ 0` (the only exponents the mission uses) this is the graph of
the closed operator `T^z` with the **support convention** `T^z = 0` on `ker T` (so `T⁰` is the
support projection), Araki–Masuda's convention for `Δ^z_{φ,Ω}` when `φ` is not faithful
(Jäkel–Robl, arXiv:1103.3608v2, §3, pp.4–6; (8), p.5; (18), p.7). -/
def posPowGraph {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : PosSpectralCalculus H) (z : ℂ) : Set (H × H) :=
  {q | Tendsto (fun N : ℕ => T.toCalc.calculus (posCut N z) q.1) atTop (𝓝 q.2)}

end KMSHolder


