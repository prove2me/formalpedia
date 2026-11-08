-- Prove2me | Definitions.Def_MonoidProdQ_Q13
-- name    : MonoidProdQ_Q13
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:53:03.458464+00:00
-- url     : https://prove2.me/theorems/e5739011-a721-47ee-96cc-879a888ce21e
-- title:
--   Bounded-error quantum query complexity $Q_{1/3}$
-- statement:
--   For a function $f$ on a promise domain $D\subseteq\Sigma^I$, the **bounded-error quantum query complexity** $Q_{1/3}(f)$ is the minimum number $T$ of quantum queries needed to compute $f$ with error probability at most $1/3$ on every input of $D$: the least $T$ for which some $T$-query algorithm, with some finite workspace, computes $f$ on $D$ with bounded error.
--
--   **Formalization Note** The value is an extended natural number, and it is $\infty$ if no algorithm exists, never a default $0$. Workspaces are of the form $\{0,\dots,m-1\}$ for some $m$, which loses nothing since every finite workspace is equivalent to one of these.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Query model, pp.21–22

import Definitions.Def_MonoidProdQ_ComputesBoundedError
open QAlgorithms

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, pp.21–22: "We write Q_{1/3}(f) for the minimum number of quantum queries needed to
compute f with error probability at most 1/3 on every input": the least `T` such that some
`T`-query algorithm, with some finite workspace, computes `f` on `D` with bounded error
(`ComputesBoundedError`).

**Formalization Note.** The value is in `ℕ∞` (an infimum over a set of naturals, attained when
nonempty), and is `⊤` when no algorithm exists, never a junk `0`. A finite workspace is
`Fin m` for some `m` (every finite workspace is equivalent to one of these). -/
noncomputable def Q13 {I Sig Out : Type*} [Fintype I] [DecidableEq I] [Fintype Sig]
    [DecidableEq Sig] [DecidableEq Out] (f : (I → Sig) → Out) (D : Finset (I → Sig)) : ℕ∞ :=
  ⨅ (T : ℕ) (_ : ∃ (m : ℕ) (A : QueryAlg I (Sig → ZMod 2) (Fin m) T)
      (out : (I × (Sig → ZMod 2)) × Fin m → Out), ComputesBoundedError f D A out), (T : ℕ∞)

end MonoidProdQ


