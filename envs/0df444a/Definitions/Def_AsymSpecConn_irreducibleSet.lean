-- Prove2me | Definitions.Def_AsymSpecConn_irreducibleSet
-- name    : AsymSpecConn_irreducibleSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:40:24.049204+00:00
-- url     : https://prove2.me/theorems/3e04ac60-fe23-47d0-92e5-16ae4d023a35
-- title:
--   $i$-irreducible tensors $\mathcal A_i$ and jointly irreducible tensors $\mathcal B$
-- statement:
--   Let $i\in[k]$. An element of $\mathcal S=\mathcal S_{\mathbb C}$ is **$i$-irreducible** if it has a concise representative $a\in V_1\otimes\dots\otimes V_k$ for which there are a finite group $G$ and representations $\rho_j:G\to\mathrm{GL}(V_j)$, $j\in[k]$, such that $\rho_i$ is irreducible and $(\rho_1(g)\otimes\dots\otimes\rho_k(g))a=a$ for every $g\in G$. $\mathcal A_i$ is the set of $i$-irreducible elements.
--
--   An element is **jointly irreducible** if it has such a representative and group with $\rho_j$ irreducible for every $j\in[k]$. $\mathcal B$ is the set of jointly irreducible elements.
--
--   These are the sets to which the abstract decomposition method is applied for tensors.
--
--   **Formalization Note** $G$ ranges over `Type`, which loses nothing because every finite group has an isomorphic copy there. Irreducibility is Mathlib's `Representation.IsIrreducible`, which excludes the zero space, so $0\notin\mathcal A_i$.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), §3.1, p.21

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_AsymSpecConn_flatRank

set_option autoImplicit false

namespace AsymSpecConn

/-- **`i`-irreducible tensors `A_i`** (§3.1, p.21 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)). An element `s` of
`S = S_ℂ` is `i`-irreducible if it has a concise representative `a ∈ V₁ ⊗ ⋯ ⊗ V_k` for which there
are a finite group `G` and representations `ρ_j : G → GL(V_j)` (`j ∈ [k]`) such that `ρ_i` is
irreducible and `(ρ₁(g) ⊗ ⋯ ⊗ ρ_k(g)) a = a` for every `g ∈ G`.

**Formalization Note** `G : Type` (every finite group has an isomorphic copy there).
`Representation.IsIrreducible` is Mathlib's notion (`IsSimpleOrder` of subrepresentations),
which excludes the zero space; so `0 ∉ A_i`. -/
def irreducibleSet {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : Set (MME.TensorQ ℂ k) :=
  {s | ∃ X : MME.TensorObj ℂ k, MME.TensorQ.toQ X = s ∧ IsConcise hk X ∧
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (ρ : ∀ j, Representation ℂ G (X.V j)),
      (ρ i).IsIrreducible ∧ ∀ g : G, PiTensorProduct.map (fun j => ρ j g) X.t = X.t}

/-- **Jointly irreducible tensors `B`** (§3.1, p.21 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): elements with a concise
representative `a` and one finite group `G` with representations `ρ_j : G → GL(V_j)` for every leg,
all irreducible, whose simultaneous action fixes `a`. (Same conventions as `irreducibleSet`.) -/
def jointlyIrreducibleSet {k : ℕ} (hk : 2 ≤ k) : Set (MME.TensorQ ℂ k) :=
  {s | ∃ X : MME.TensorObj ℂ k, MME.TensorQ.toQ X = s ∧ IsConcise hk X ∧
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (ρ : ∀ j, Representation ℂ G (X.V j)),
      (∀ j, (ρ j).IsIrreducible) ∧ ∀ g : G, PiTensorProduct.map (fun j => ρ j g) X.t = X.t}

end AsymSpecConn


