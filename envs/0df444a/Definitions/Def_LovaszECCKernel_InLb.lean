-- Prove2me | Definitions.Def_LovaszECCKernel_InLb
-- name    : LovaszECCKernel_InLb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:50.921606+00:00
-- url     : https://prove2.me/theorems/07734945-53cd-4bf9-b66c-2822fc454544
-- title:
--   Yes-instances of ECC below the Lovász bound: $\mathrm{ecc}(G)\le\mathrm{Lb}(G)-k$
-- statement:
--   An instance of **Edge Clique Cover below the Lovász bound** is a pair $(G,k)$ of a finite simple graph and an integer $k\ge 0$. It is a **yes-instance** when the edges of $G$ can be covered by at most $\mathrm{Lb}(G)-k$ cliques:
--   $$\mathrm{ecc}(G)\le\mathrm{Lb}(G)-k .$$
--
--   **Formalization Note** The inequality is between integers: $\mathrm{Lb}(G)-k$ may be negative, and then $(G,k)$ is a no-instance. $k$ is a natural number.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 3, p.4, and §3, p.19 (= PDF pp.4, 19)

import Mathlib
import Definitions.Def_LovaszECCKernel_Lb
import Definitions.Def_LovaszECCKernel_ecc

set_option autoImplicit false

namespace LovaszECCKernel

/-- `(G, k)` is a **yes-instance of ECC below the Lovász bound** (Fomin, Golovach, Khargeliia,
Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic Extensions of the Lovász and
Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 3, p.4
(= PDF p.4)): "The problem of deciding whether the edges of a graph G can be covered by at most
Lb(G) − k cliques", i.e. `ecc(G) ≤ Lb(G) − k` (§3, p.19).

**Formalization Note** The comparison is in `ℤ`: `Lb(G) − k` may be negative, and then `(G, k)` is a
no-instance. The parameter `k` is a natural number (the paper's "integer k ≥ 0", p.41). -/
def InLb {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  (ecc G : ℤ) ≤ (Lb G : ℤ) - k

end LovaszECCKernel


