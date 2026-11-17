-- Prove2me | Definitions.Def_LovaszECCKernel_Supplement_InEGP
-- name    : LovaszECCKernel_Supplement_InEGP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:10:31.34681+00:00
-- url     : https://prove2.me/theorems/26d40622-03f2-4ee9-acb9-3d4ea94e0705
-- title:
--   ECP below the Erdős–Goodman–Pósa bound — yes-instances and equivalent kernel outputs
-- statement:
--   For a graph $G$ on $n$ vertices and an integer $k\ge0$, the instance $(G,k)$ of **Edge Clique Partition below the Erdős–Goodman–Pósa bound** is a yes-instance if
--   $$\mathrm{ecp}(G)\ \le\ \Big\lfloor\frac{n^2}{4}\Big\rfloor-k .$$
--   A kernel output (a list of numbers decoded by the mission's fixed instance decoding into a graph $G'$ and a parameter $k'$) is **equivalent** to $(G,k)$ if $(G',k')$ is a yes-instance exactly when $(G,k)$ is.
--
--   These are the yes-instances and the equivalence notion of the paper's Theorem 4.
--
--   **Formalization Note** $\lfloor n^2/4\rfloor$ is integer division of $n^2$ by $4$; the comparison is made in $\mathbb Z$, so when $\lfloor n^2/4\rfloor<k$ the instance is a no-instance (never truncated to $0$). Outputs are decoded by the published `decodeInstance`.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 4, p.5 (= PDF p.5); kernel equivalence §2, p.16

import Mathlib
import Definitions.Def_LovaszECCKernel_Supplement_ecp
import Definitions.Def_LovaszECCKernel_decodeInstance

set_option autoImplicit false

namespace LovaszECCKernel.Supplement

/-- `(G, k)` is a **yes-instance of ECP below the Erdős–Goodman–Pósa bound** (Fomin, Golovach,
Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic Extensions of the Lovász and
Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 4, p.5
(= PDF p.5)): "deciding whether the edges of a graph G could be partitioned into at most ⌊n²/4⌋ − k
cliques", i.e. `ecp(G) ≤ ⌊n²/4⌋ − k` with `n = |V(G)|`.

**Formalization Note** `⌊n²/4⌋` is the natural-number division `n ^ 2 / 4`; the comparison is in `ℤ`,
so a negative right-hand side makes `(G, k)` a no-instance. The parameter `k` is a natural number. -/
def InEGP {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  (ecp G : ℤ) ≤ ((Fintype.card V ^ 2 / 4 : ℕ) : ℤ) - k

/-- The output `out` decodes (by the published `decodeInstance`) to an instance `(G′, k′)` of ECP
below the Erdős–Goodman–Pósa bound **equivalent** to `(G, k)` (Fomin et al., STOC 2027 submission
(manuscript sha256 a9d53ab8…), §2, p.16 (= PDF p.16): "(i) (x, k) ∈ L if and only if (x′, k′) ∈ L"):
`ecp(G′) ≤ ⌊n′²/4⌋ − k′ ⟺ ecp(G) ≤ ⌊n²/4⌋ − k`. -/
def KernelEquivEGP {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (out : List ℕ) : Prop :=
  ∃ n' : ℕ, ∃ G' : SimpleGraph (Fin n'), ∃ k' : ℕ, decodeInstance out = some ⟨n', G', k'⟩ ∧
    (InEGP G' k' ↔ InEGP G k)

end LovaszECCKernel.Supplement


