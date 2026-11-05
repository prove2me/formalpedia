-- Prove2me | Definitions.Def_KMSHolder_modPowGraph
-- name    : KMSHolder_modPowGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:56.309195+00:00
-- url     : https://prove2.me/theorems/e6f76e9b-66cf-4440-8468-72eea5e67384
-- title:
--   Graph of the modular power $\Delta^z$
-- statement:
--   Let $\Delta$ be the modular operator of a von Neumann algebra with cyclic and separating unit vector $\Omega$ and $z \in \mathbb C$. The **graph of $\Delta^z$** is the set of pairs $(x, y) \in H \times H$ such that
--
--   $$
--   e_{N,z}(\log\Delta)\, x \longrightarrow y \qquad (N \to \infty),
--   $$
--
--   where $e_{N,z}(u) = \exp(z \cdot \max(-N, \min(N,u)))$ are the bounded cut-offs of $u \mapsto e^{zu}$. For $\Re z \ge 0$ this is the graph of the closed operator $\Delta^z$: $x$ lies in its domain exactly when the cut-offs converge, and then $y = \Delta^z x$. The paper uses $\Delta^{1/2p}A\Omega$ in Lemmas 4.1 and 4.2, and writes $\Delta^z$ as $e^{-z\beta L}$ for a KMS state.
--
--   **Formalization Note** $\log\Delta$ is the calculus `S.D` of the published `StandardModularData`. For $z = 1/2$ the set equals the published `S.D.halfGraph` (checked by a proved sanity lemma), and for $z = is$ it is the graph of `S.D.unitary s`.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, p.2 (Δ^{1/2} = e^{−βL/2}), p.4; eqs. (18)–(19), p.7; (28), p.8

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_KMSHolder_expCut

open OAI.BoundedRecovery
open Filter Topology

namespace KMSHolder

/-- The graph of `Δ^z`, `Δ` the modular operator of standard modular data `S`
(Jäkel–Robl, arXiv:1103.3608v2: `Δ^{1/2} ≡ e^{−βL/2}`, p.2 and p.4; the powers `Δ^{1/2p}AΩ` of
(18)–(19), p.7, and (28), p.8): `(x, y)` with `expCut N z (D) x → y` as `N → ∞`, where
`D = S.D` is the calculus of `log Δ`.

**Formalization Note.** For `ℜz ≥ 0` (the only exponents the mission uses), dominated
convergence makes this exactly the graph of the closed operator `Δ^z = e^{zD}`: `x` is in the
domain iff the cut-offs converge, and then the limit is `Δ^z x`. `modPowGraph S (1/2)` is the
platform's `S.D.halfGraph` (verified in `Solutions/verification/KMSHolder_sanity.lean`), and
`modPowGraph S (s * I)` is the graph of `S.D.unitary s`. -/
def modPowGraph {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StandardModularData H) (z : ℂ) : Set (H × H) :=
  {q | Tendsto (fun N : ℕ => S.D.calculus (expCut N z) q.1) atTop (𝓝 q.2)}

end KMSHolder


