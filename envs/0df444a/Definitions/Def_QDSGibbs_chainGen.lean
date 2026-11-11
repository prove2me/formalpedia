-- Prove2me | Definitions.Def_QDSGibbs_chainGen
-- name    : QDSGibbs_chainGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:41.636535+00:00
-- url     : https://prove2.me/theorems/9f30da01-8d83-4ba9-9366-80260de58e63
-- title:
--   Intervals, neighbourhoods, boundary neighbourhoods $C_u(B)$, the labelled blocks $\mathcal W_\ell$, and the sampler generator $\mathcal L$
-- statement:
--   On the chain $[N]$ with $\mathrm{dist}(i,j)=|i-j|$: an **interval** is a nonempty set of consecutive sites; $U^{\le a}=\{i:\mathrm{dist}(i,U)\le a\}$; two sets are at distance at least $v$ when every pair of their points is. For an interval $B=[a,b]$ with boundary bonds $\partial B=\{a-1,b\}\cap\{1,\dots,N-1\}$, the **boundary neighbourhood** and **interior** are
--
--   $$
--   C_u(B)=[N]\cap\bigcup_{q\in\partial B}[q-u,q+u+1],\qquad I_u(B)=B\setminus C_u(B).
--   $$
--
--   For $\ell\ge2$ the **labelled blocks** are $\mathcal W_\ell=(B_a)_{a=2-\ell}^N$, $B_a=[a,a+\ell-1]\cap[N]$, keeping distinct labels when intervals coincide (each site lies in exactly $\ell$ labelled blocks). The **sampler** is
--
--   $$
--   \mathcal L=\frac1\ell\sum_{B\in\mathcal W_\ell}(\Phi_B-\mathrm{id}),\qquad \Phi_B=e^{T\mathcal K_B}.
--   $$
--
--   **Formalization Note** 0-based sites. Labels are $k\in\{0,\dots,N+\ell-2\}$, label $k$ being the paper's $a=k+2-\ell$, with block $\{i:k+1\le i+\ell,\ i\le k\}$. $C_u(B)$ is defined through the bonds $(b,b+1)$ with exactly one endpoint in $B$; for an interval these are the boundary bonds of (5.6), and for $B=[N]$ the set is empty.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), §2.1, p.10; (5.2), p.39; (5.6)–(5.7), p.40

import Mathlib
import Definitions.Def_QDSGibbs_blockChannel

open scoped Matrix

namespace QDSGibbs

/-- An **interval** of the chain `[N]`: a nonempty set of consecutive sites (arXiv:2610.03578, held
file sha256 ede55815…, §5, p.40, "`B = [a, b] ∩ ℤ ⊆ [N]`"). -/
def IsInterval {N : ℕ} (B : Finset (Fin N)) : Prop :=
  B.Nonempty ∧ ∀ i j k : Fin N, i ∈ B → k ∈ B → i ≤ j → j ≤ k → j ∈ B

open Classical in
/-- The neighbourhood `U^{≤a} = {i ∈ Λ : dist(i, U) ≤ a}` on the chain, `dist(i, j) = |i − j|`
(arXiv:2610.03578, §2.1, p.10; §5, p.39). Empty for `U = ∅`. -/
noncomputable def nbhd {N : ℕ} (U : Finset (Fin N)) (a : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => ∃ j ∈ U, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ a

/-- Two sets of sites are at distance at least `v`: `dist(S, T) = inf_{i ∈ S, j ∈ T} |i − j| ≥ v`
(arXiv:2610.03578, §2.1, p.10; `inf ∅ = +∞`, so this holds when one set is empty). -/
def DistGe {N : ℕ} (S T : Finset (Fin N)) (v : ℝ) : Prop :=
  ∀ i ∈ S, ∀ j ∈ T, v ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|

open Classical in
/-- The **boundary neighbourhood** `C_u(B) = [N] ∩ ⋃_{q ∈ ∂B} [q − u, q + u + 1]` (arXiv:2610.03578,
(5.6)–(5.7), p.40).

**Formalization Note** 0-based sites. A bond is a pair of sites `(b, b+1)`; it crosses `B` when
exactly one endpoint lies in `B`. For an interval `B` the crossing bonds are exactly the bonds
`{q, q+1}`, `q ∈ ∂B`, of (5.6) (paper bond `q` = 0-based sites `q−1, q`), and the sites `b − u, …,
b + 1 + u` are the paper's `[q − u, q + u + 1]`. For `B = [N]` it is empty. -/
noncomputable def bdryNbhd {N : ℕ} (B : Finset (Fin N)) (u : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => ∃ b c : Fin N, (c : ℕ) = (b : ℕ) + 1 ∧ (b ∈ B ↔ c ∉ B) ∧
    (b : ℕ) ≤ (i : ℕ) + u ∧ (i : ℕ) ≤ (c : ℕ) + u

/-- The **interior** `I_u(B) = B ∖ C_u(B)` (arXiv:2610.03578, (5.7), p.40). -/
noncomputable def interiorU {N : ℕ} (B : Finset (Fin N)) (u : ℕ) : Finset (Fin N) :=
  B \ bdryNbhd B u

/-- The **labelled blocks** `W_ℓ = (B_a)_{a = 2−ℓ}^{N}`, `B_a = [a, a + ℓ − 1] ∩ [N]`
(arXiv:2610.03578, §5, p.39).

**Formalization Note** Labels are `k : Fin (N + ℓ − 1)`, label `k` being the paper's `a = k + 2 − ℓ`;
with 0-based sites, `B_k = {i : k + 1 ≤ i + ℓ ∧ i ≤ k}`. Coinciding intervals keep distinct labels
(also when `N < ℓ`), and every site lies in exactly `ℓ` labels. -/
def block (N ℓ : ℕ) (k : Fin (N + ℓ - 1)) : Finset (Fin N) :=
  Finset.univ.filter fun i : Fin N => (k : ℕ) + 1 ≤ (i : ℕ) + ℓ ∧ (i : ℕ) ≤ (k : ℕ)

/-- The **QBP block Gibbs sampler** generator `L = ℓ^{−1} Σ_{B ∈ W_ℓ} (Φ_B − id)`, `Φ_B = e^{T K_B}`
(arXiv:2610.03578, (5.2), p.39), for the chain `H = Σ V_i + Σ W_i`. -/
noncomputable def chainGen {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (V : Fin N → Op d)
    (W : Fin (N - 1) → Op d) (ℓ : ℕ) (T : ℝ) (X : Op d) : Op d :=
  ((ℓ : ℂ))⁻¹ • ∑ k : Fin (N + ℓ - 1),
    (blockChannel β (chain V W) (block N ℓ k) Finset.univ T X - X)

end QDSGibbs


