-- Prove2me | Definitions.Def_BlockchainTFM_Properties
-- name    : BlockchainTFM_Properties
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:40.328601+00:00
-- url     : https://prove2.me/theorems/1be546c5-a7c8-43ef-9c0c-f0c584a357bd
-- title:
--   U-DSIC, U-BNIC, 1-SCP, UIR, BF and $(C,N)$-U-SP of a transaction fee mechanism
-- statement:
--   This module defines the incentive, collusion, rationality and feasibility properties of §3.3–3.4. Throughout, valuations are i.i.d. from a law $V_0$ on $[0,1]$, and $\mathbf b_{-i}$ ranges over $[0,1]^{n-1}$.
--
--   1. **U-DSIC** (Definition 3). For every user $i$, every $\mathbf b_{-i}$ and every value $v_i\in[0,1]$, bidding $v_i$ maximizes $u_i(\cdot,\mathbf b_{-i};v_i)$ over bids in $[0,1]$.
--   2. **Interim U-BNIC** (Definition 4). When the other users bid their valuations, bidding her valuation maximizes user $i$'s expected utility:
--   $$v_i\in\arg\max_{b_i}\ \mathbb E_{\mathbf b_{-i}\sim V_{-i}}\bigl[u_i(b_i,\mathbf b_{-i};v_i)\bigr],$$
--   with $V_{-i}=V_0^{\,n-1}$; the expectations are required to exist.
--   3. **1-SCP** (Definition 6 with $c=1$). The miner and one user $i$ cannot strictly increase their total utility by changing user $i$'s bid, ex post: for all $\mathbf b_{-i}$ and $v,x\in[0,1]$,
--   $$u_i(x,\mathbf b_{-i};v)+r(x,\mathbf b_{-i})\le u_i(v,\mathbf b_{-i};v)+r(v,\mathbf b_{-i}).$$
--   4. **UIR** (§3.4). $u_i(v_i,\mathbf b_{-i};v_i)\ge 0$ for every $\mathbf b_{-i}$ and $v_i$.
--   5. **BF** (§3.4, (4)). $r(\mathbf b)\le P(\mathbf b)=\sum_{i=1}^n a_i(\mathbf b)\,p_i(\mathbf b)$ for every bid vector.
--   6. **$(C,N)$-U-SP** (Definitions 1′ and 5). For a variable-bid-size TFM $\mathcal M=(M_\eta)_\eta$ (the mechanism $M_\eta$ is used when $\eta$ bids are presented, (1)): for every $n>N$, every real user $i$ bidding her value $v_i=b_i$, every number $l\le Cn$ of fake bids and every fake bid vector $\mathbf b^\#=(b_{n+1},\dots,b_{n+l})\in[0,1]^l$,
--   $$\mathbb E_{\mathbf b_{-i}\sim V_{-i}}\bigl[u_i(b_i,\mathbf b_{-i};v_i)\bigr]\ \ge\ \mathbb E_{\mathbf b_{-i}\sim V_{-i}}\Bigl[u_i(b_i,\mathbf b^+_{-i};v_i)+\sum_{j=n+1}^{n+l}u_j(b_j,\mathbf b^+_{-j};0)\Bigr],$$
--   where $\mathbf b^+=(b_1,\dots,b_{n+l})$; fake identities value confirmation at $0$.
--
--   These are the properties asserted by Theorem 4 and characterized by Lemma 1 and Lemma EC.3.
--
--   **Formalization Note** Expectations are Bochner integrals against the product measure $V_0^{\otimes n}$ with coordinate $i$ overwritten by user $i$'s bid, which equals integration over $\mathbf b_{-i}$. U-BNIC and U-SP require the integrands to be integrable, so that a non-existent expectation (which Lean evaluates to $0$) cannot make the inequality hold vacuously. U-BNIC is imposed for every $v_i\in[0,1]$. U-SP carries an extra lower bound $n\ge n_0$ on the number of real users, used by Theorem 4 because its mechanism family is specified only for $n\ge\max\{\lambda_0k,30\}$; with $n_0=0$ it is Definition 5. With $l$ fake bids the bid vector is the concatenation of the $n$ real bids and the $l$ fake bids.
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, §3.3–3.4, Definition 1′ and (1) p.17, Definitions 3, 4, 5 and the display after Definition 5 p.18, Definition 6 p.19, UIR and BF (4) p.19

import Mathlib
import Definitions.Def_BlockchainTFM_Model

open MeasureTheory

namespace BlockchainTFM

/-- **Interim expected utility** of user `i`, arXiv:2209.13099v7, Definition 4, p.18:
`E_{b_{-i} ∼ V_{-i}}[u_i(x, b_{-i}; v)]`, where the other users bid their valuations, drawn
i.i.d. from `V₀`.

**Formalization Note.** The expectation is the Bochner integral against the product law
`Measure.pi (fun _ => V₀)` on all `n` coordinates, with coordinate `i` overwritten by the bid `x`
(`Function.update b i x`); since coordinate `i` is overwritten, this equals the integral over
`b_{-i}` alone. Valuations are independent, so the law of `b_{-i}` given `v_i` is
`V₀^{n−1}`. -/
noncomputable def interimUtility {n : ℕ} (V₀ : Measure ℝ) (M : TFM n) (i : Fin n) (x v : ℝ) :
    ℝ :=
  ∫ b, utility M i (Function.update b i x) v ∂(Measure.pi fun _ : Fin n => V₀)

/-- **U-DSIC**, arXiv:2209.13099v7, Definition 3, p.18: for every user `i` and every `b_{-i}`,
bidding the valuation `v_i` maximizes `u_i(·, b_{-i}; v_i)` over bids in `[0,1]`.

**Formalization Note.** `b ∈ bidBox n` ranges over the other users' bids (its `i`-th entry is
overwritten); `v` and the deviation `x` range over `[0,1]`. -/
def IsUDSIC {n : ℕ} (M : TFM n) : Prop :=
  ∀ i : Fin n, ∀ b ∈ bidBox n, ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    utility M i (Function.update b i x) v ≤ utility M i (Function.update b i v) v

/-- **(Interim) U-BNIC**, arXiv:2209.13099v7, Definition 4, p.18: when the other users bid their
valuations (i.i.d. `V₀`), bidding her own valuation maximizes user `i`'s expected utility:
`v_i ∈ argmax_{b_i} E_{b_{-i}∼V_{-i}}[u_i(b_i, b_{-i}; v_i)]`.

**Formalization Note.** The expectations are required to exist: for every `i`, bid `x ∈ [0,1]`
and value `v ∈ [0,1]` the integrand is integrable (a Bochner integral of a non-integrable
function is `0` in Lean, which would make the inequality vacuous). The condition is imposed for
every `v ∈ [0,1]`, not only `V₀`-almost every `v`. -/
def IsUBNIC {n : ℕ} (V₀ : Measure ℝ) (M : TFM n) : Prop :=
  ∀ i : Fin n, ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Integrable (fun b => utility M i (Function.update b i x) v)
        (Measure.pi fun _ : Fin n => V₀) ∧
      interimUtility V₀ M i x v ≤ interimUtility V₀ M i v v

/-- **1-SCP** (side-contract-proofness with `c = 1`), arXiv:2209.13099v7, Definition 6, p.19:
the miner and one user `i` cannot strictly increase their total utility `u_i + r` by changing
user `i`'s bid, whatever the other users' bids (ex post: the miner knows all valuations and bids;
the other users bid truthfully, which is their Bayes–Nash equilibrium under U-BNIC).

**Formalization Note.** For every `i`, every `b_{-i} ∈ [0,1]^{n−1}` (the entry `b i` is
overwritten), every value `v ∈ [0,1]` and every deviation `x ∈ [0,1]`:
`u_i(x, b_{-i}; v) + r(x, b_{-i}) ≤ u_i(v, b_{-i}; v) + r(v, b_{-i})`. This is the
coalition deviation the paper analyses (Lemma EC.3). -/
def IsOneSCP {n : ℕ} (M : TFM n) : Prop :=
  ∀ i : Fin n, ∀ b ∈ bidBox n, ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    utility M i (Function.update b i x) v + M.rev (Function.update b i x) ≤
      utility M i (Function.update b i v) v + M.rev (Function.update b i v)

/-- **(Ex-post) UIR**, arXiv:2209.13099v7, §3.4, p.19: each user gets non-negative utility when
bidding truthfully, no matter how others bid: `∀ b_{-i}, u_i(v_i, b_{-i}; v_i) ≥ 0`. -/
def IsUIR {n : ℕ} (M : TFM n) : Prop :=
  ∀ i : Fin n, ∀ b ∈ bidBox n, ∀ v ∈ Set.Icc (0 : ℝ) 1,
    0 ≤ utility M i (Function.update b i v) v

/-- **(Ex-post) BF**, arXiv:2209.13099v7, §3.4, (4), p.19: for every bid vector `b` the miner's
revenue is at most the total user payment `P(b) = ∑_i a_i(b) p_i(b)`. -/
def IsBF {n : ℕ} (M : TFM n) : Prop :=
  ∀ b ∈ bidBox n, M.rev b ≤ ∑ i, M.alloc b i * M.pay b i

/-- **(Interim) `(C, N)`-U-SP** of a variable-bid-size TFM, arXiv:2209.13099v7, Definition 1′
and (1), p.17, and Definition 5 with the display after it, p.18.

`M η` is the mechanism used when `η` bids are presented. For every number of real users `n`
with `n > N` (and `n ≥ n₀`, see the note), every real user `i` with value `v ∈ [0,1]` bidding
truthfully, every number `l` of fake bids with `l ≤ C n` and every fake bid vector
`f ∈ [0,1]^l`, user `i`'s expected utility without fake bids is at least her expected utility
with them plus the utilities of the fake identities, each valuing confirmation at `0`:
`E[u_i(b_i, b_{-i}; v_i)] ≥ E[u_i(b_i, b⁺_{-i}; v_i) + ∑_{j=n+1}^{n+l} u_j(b_j, b⁺_{-j}; 0)]`,
the expectations over the other real users' truthful bids, i.i.d. `V₀`.

**Formalization Note.** The bid vector with fakes is `Fin.append b f : Fin (n + l) → ℝ`; real
user `i` is `Fin.castAdd l i` and fake `j` is `Fin.natAdd n j`. Both integrands are required to
be integrable. The extra lower bound `n₀ ≤ n` restricts the property to the range of bid counts
on which the mechanism family is specified (Theorem 4 defines its mechanism only for
`n ≥ max{λ₀k, 30}`); with `n₀ = 0` it is exactly Definition 5. -/
def IsUSP (V₀ : Measure ℝ) (M : (η : ℕ) → TFM η) (C N n₀ : ℝ) : Prop :=
  ∀ n : ℕ, n₀ ≤ (n : ℝ) → N < (n : ℝ) →
    ∀ i : Fin n, ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ l : ℕ, (l : ℝ) ≤ C * n →
      ∀ f : Fin l → ℝ, (∀ j, f j ∈ Set.Icc (0 : ℝ) 1) →
        Integrable (fun b => utility (M n) i (Function.update b i v) v)
            (Measure.pi fun _ : Fin n => V₀) ∧
        Integrable (fun b =>
            utility (M (n + l)) (Fin.castAdd l i) (Fin.append (Function.update b i v) f) v +
              ∑ j : Fin l,
                utility (M (n + l)) (Fin.natAdd n j) (Fin.append (Function.update b i v) f) 0)
            (Measure.pi fun _ : Fin n => V₀) ∧
        (∫ b, (utility (M (n + l)) (Fin.castAdd l i) (Fin.append (Function.update b i v) f) v +
              ∑ j : Fin l,
                utility (M (n + l)) (Fin.natAdd n j) (Fin.append (Function.update b i v) f) 0)
            ∂(Measure.pi fun _ : Fin n => V₀)) ≤
          ∫ b, utility (M n) i (Function.update b i v) v ∂(Measure.pi fun _ : Fin n => V₀)

end BlockchainTFM


