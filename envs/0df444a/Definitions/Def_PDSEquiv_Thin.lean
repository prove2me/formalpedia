-- Prove2me | Definitions.Def_PDSEquiv_Thin
-- name    : PDSEquiv_Thin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:40.421211+00:00
-- url     : https://prove2.me/theorems/93bd5430-57d0-49c3-9066-a1cea8e16d23
-- title:
--   Thinning $\mathrm{Thin}_n(G,v,t)$, the vertex score $Z_v$, $h$, $\theta$, $L$, the conditional means $\mu_s$ and condition (8)
-- statement:
--   1. **Thinning.** For a graph $G$ on $[N]$, a vertex $v$ and $t\in[0,1]$, $H=\mathrm{Thin}_n(G,v,t)$ chooses a uniform $n$-subset $A\subseteq[N]\setminus\{v\}$, a set $S\sim\mathrm{Bin}(A,t)$ independent of $G$, puts $W=S\setminus\Gamma_G[v]$ ($\Gamma_G[v]$ the closed neighbourhood), keeps the edges of $G$ inside $W$, resamples every other pair from $\mathrm{Ber}(q)$, and relabels $A$ by a uniform bijection onto $[n]$.
--   2. $\theta=(1-p)/(1-q)$ (9), and $L$ is the least positive integer with $\theta^L\le N^{-2}$, with the convention $0^0=1$.
--   3. For an oracle with acceptance probabilities $a$ on $n$-vertex graphs, $h(x)=\Pr_{H\sim\widetilde{\mathrm{PDS}}(n,x,p,q)}[O(H)=1]$ and the score $Z_v(G)=\Pr[O(\mathrm{Thin}_n(G,v,\theta^\ell))=1]$ with $\ell$ uniform on $\{0,\dots,L-1\}$.
--   4. $\mu_s=\mathbb E[Z_v(G)\mid \mathbf 1\{v\in C\}=s]$ over $(G,C)\sim\widetilde{\mathrm{PDS}}(N,K,p,q)$, and conditional probabilities of events given $\mathbf 1\{v\in C\}=s$.
--   5. Condition (8): $\Pr_{\mathrm{ER}(n,q)}[O=1]\le\gamma/8$ and $\Pr_{\mathrm{PDS}(n,j,p,q)}[O=1]\ge\gamma$ for every $\kappa\le j\le n$.
--
--   These are the objects of the search-to-decision reduction of §7.
--
--   **Formalization Note** The choice of $A$ and the relabeling together are one uniform injection $[n]\to[N]\setminus\{v\}$, which is what the mass averages over; $S$ is written on the labels. Conditional means are ratios of finite sums; their denominators are positive when $1\le K\le N-1$. Lean's $0^0=1$ is the paper's convention, so at $p=1$ ($\theta=0$) the least $L$ is $1$.
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), §7.1, p.26 (h, (8)); §7.2, pp.26–28 (Thin_n, (9), L, Z_v, μ_s)

import Mathlib
import Definitions.Def_PDSEquiv_Laws

set_option autoImplicit false

namespace PDSEquiv

noncomputable section

/-!
# Thinning, vertex scores, `h`, `μ_s`, and condition (8)

S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), §7.1–7.2, pp.26–28.

**Formalization Note.** `a : Graph n → ℝ` is the acceptance function of a randomized distinguisher on
`n`-vertex graphs, with values in `[0, 1]`. In `Thin_n` the page draws a uniform `n`-subset `A` of
`[N] \ {v}` and a uniform bijection `A → [n]`; together they are one uniform injection
`φ : [n] → [N] \ {v}`, which is what `thinMass` averages over, and `S ∼ Bin(A, t)` is written on the
labels. `levelL` is an infimum over a set of naturals, nonempty for `0 ≤ θ < 1` and `N ≥ 1`. Lean's
`0 ^ 0 = 1` is the page's convention, so at `p = 1` (`θ = 0`) the least `L` is `1`.
-/

/-- `θ = (1 − p)/(1 − q)`, display (9), p.27. -/
def theta (p q : ℝ) : ℝ := (1 - p) / (1 - q)

/-- The least positive integer `L` with `θ^L ≤ N^{−2}`, p.27. -/
def levelL (p q : ℝ) (N : ℕ) : ℕ :=
  sInf {L : ℕ | 0 < L ∧ theta p q ^ L ≤ ((N : ℝ) ^ 2)⁻¹}

/-- `Γ_G[v]`, the closed neighbourhood: membership of `u`. -/
def inClosedNbhd {N : ℕ} (G : Graph N) (v u : Fin N) : Prop := u = v ∨ gAdj G u v = true

open Classical in
/-- The mass of `H = Thin_n(G, v, t)`, pp.26–27. `φ` is the uniform injection into `[N] \ {v}` (the
choice of `A` and the relabeling), `S` the retained labels (`S ∼ Bin(A, t)`), `W` those retained
labels whose vertex is outside `Γ_G[v]`. A pair inside `W` is copied from `G`; every other pair is a
fresh `Ber(q)`. -/
def thinMass {n N : ℕ} (q t : ℝ) (G : Graph N) (v : Fin N) (H : Graph n) : ℝ :=
  (Fintype.card {φ : Fin n ↪ Fin N // ∀ i, φ i ≠ v} : ℝ)⁻¹ *
    ∑ φ : {φ : Fin n ↪ Fin N // ∀ i, φ i ≠ v}, ∑ S : Finset (Fin n),
      t ^ S.card * (1 - t) ^ (n - S.card) *
        ∏ e : Pair n,
          if (e.1.1 ∈ S ∧ ¬ inClosedNbhd G v (φ.1 e.1.1)) ∧
              (e.1.2 ∈ S ∧ ¬ inClosedNbhd G v (φ.1 e.1.2)) then
            (if H e = gAdj G (φ.1 e.1.1) (φ.1 e.1.2) then 1 else 0)
          else ber q (H e)

/-- `h(x) = Pr_{H∼P̃DS(n,x,p,q)}[O(H) = 1]`, p.26. -/
def hFun {n : ℕ} (p q : ℝ) (a : Graph n → ℝ) (x : ℝ) : ℝ := expect (pdsbMass n x p q) a

/-- The score `Z_v(G) = Pr[O(Thin_n(G, v, θ^ℓ)) = 1]`, `ℓ` uniform on `{0, …, L − 1}`, p.27. -/
def scoreZ {n N : ℕ} (p q : ℝ) (a : Graph n → ℝ) (G : Graph N) (v : Fin N) : ℝ :=
  ((levelL p q N : ℝ))⁻¹ * ∑ ℓ ∈ Finset.range (levelL p q N),
    ∑ H, thinMass q (theta p q ^ ℓ) G v H * a H

open Classical in
/-- `Pr_{(G,C)∼P̃DS(N,K,p,q)}[(G, C) ∈ E | 1{v ∈ C} = s]`, as a ratio of finite sums. -/
def condProb {N : ℕ} (K p q : ℝ) (v : Fin N) (s : Bool)
    (E : Graph N → Finset (Fin N) → Prop) : ℝ :=
  (∑ G : Graph N, ∑ C : Finset (Fin N),
      if decide (v ∈ C) = s ∧ E G C then pdsbJoint N K p q G C else 0) /
    (∑ G : Graph N, ∑ C : Finset (Fin N),
      if decide (v ∈ C) = s then pdsbJoint N K p q G C else 0)

open Classical in
/-- `μ_s = E[Z_v(G) | 1{v ∈ C} = s]` over `(G, C) ∼ P̃DS(N, K, p, q)`, p.28. -/
def condMean {n N : ℕ} (K p q : ℝ) (a : Graph n → ℝ) (v : Fin N) (s : Bool) : ℝ :=
  (∑ G : Graph N, ∑ C : Finset (Fin N),
      if decide (v ∈ C) = s then pdsbJoint N K p q G C * scoreZ p q a G v else 0) /
    (∑ G : Graph N, ∑ C : Finset (Fin N),
      if decide (v ∈ C) = s then pdsbJoint N K p q G C else 0)

/-- Condition (8), p.26: `O` accepts `ER(n, q)` with probability at most `γ/8`, and `PDS(n, j, p, q)`
with probability at least `γ` for every `κ ≤ j ≤ n`. -/
def IsAdversarial {n : ℕ} (p q γ : ℝ) (κ : ℕ) (a : Graph n → ℝ) : Prop :=
  expect (erMass n q) a ≤ γ / 8 ∧ ∀ j : ℕ, κ ≤ j → j ≤ n → expect (pdsMass n j p q) a ≥ γ

end

end PDSEquiv


