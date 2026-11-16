-- Prove2me | Definitions.Def_AFIsingKS_Supplement_reweight
-- name    : AFIsingKS_Supplement_reweight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:22:26.029501+00:00
-- url     : https://prove2.me/theorems/29e81db8-8772-4dae-9aa2-60531549dd2e
-- title:
--   Short cycles $\mathcal C_k$, good families $\mathcal G(\le m)$ and the reweighting factor $A_{L,m}(\beta)$
-- statement:
--   Fix $n,d\in\mathbb N$ and consider the $dn$ **sockets** $V\times[d]$, $V=\{1,\dots,n\}$, of the configuration model; $M$ is a perfect matching of the sockets.
--
--   1. A **$k$-cycle** is a collection of $k$ pairwise disjoint socket pairs $\{(u_t,i_t),(v_t,j_t)\}$, $t=1,\dots,k$, that forms a cycle of length $k$ after each cloud $\{v\}\times[d]$ is contracted to a vertex: $v_t=u_{t+1}$ (indices mod $k$), and every cloud on it is visited exactly twice. $\mathcal C_k$ is the set of all $k$-cycles; a cycle is the set of its $k$ socket pairs, so
--   $$|\mathcal C_k|=\frac{(n)_k\,d^k(d-1)^k}{2k}.$$
--   $k=1$ gives loops and $k=2$ double edges.
--   2. For a finite set $\Gamma$ of cycles of lengths $1,\dots,L$ write $|\Gamma|=\sum_{C\in\Gamma}|C|$, where $|C|$ is the length of $C$. The **good families** $\mathcal G(\le m)$ are the sets $\Gamma\subseteq\bigcup_{k=1}^L\mathcal C_k$ of pairwise vertex-disjoint (cloud-disjoint) cycles with $|\Gamma|\le m$; the empty family is one of them. $\{\Gamma\subseteq M\}$ is the event that every socket pair of every cycle of $\Gamma$ is an edge of $M$.
--   3. With $\lambda_k=(d-1)^k/(2k)$, $\delta_k(\beta)=\big((e^{-\beta}-1)/(e^{-\beta}+1)\big)^k$ and $b_k=(1+\delta_k)^{-1}-1$ for $\beta\in\mathbb C$, the **reweighting factor** is
--   $$A_{L,m}(\beta)=\exp\Big(\sum_{k=1}^L\lambda_k\delta_k(\beta)\Big)\sum_{\Gamma\in\mathcal G(\le m)}\mathbf 1[\Gamma\subseteq M]\prod_{C\in\Gamma}b_{|C|}(\beta).$$
--   4. Theorems 5.2 and 5.3 use $L=\log\log N/\log\log\log N$ and $m=\log N/(\log\log N)^2$, $N=nd$, natural logarithms, rounded down to natural numbers.
--
--   $A_{L,m}$ is the explicit truncated small-cycle reweighting with which the paper carries out the second moment method for complex $\beta$.
--
--   **Formalization Note** A cycle is a `Finset` of `Sym2` socket pairs, built as the image of $t\mapsto\{(v_t,i_t),(v_{t+1},j_{t+1})\}$ over injective cloud sequences with $i_t\ne j_t$. Lean's $0^{-1}=0$ and $x/0=0$ only change $\delta_k,b_k$ where $e^{-\beta}=-1$ or $\delta_k=-1$, away from the segment $[0,\beta_{\mathrm{KS}}]$. Since $L$ only bounds $k\in\{1,\dots,L\}$ and $m$ only bounds the natural number $|\Gamma|$, rounding them down selects the same terms. Sanity checks $A_{L,m}(0)=1$, $|\mathcal C_1|=3$ ($n=1,d=3$), $|\mathcal C_2|=2$ ($n=d=2$), $|\mathcal C_3|=8$ ($n=3,d=2$) are proved.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2 "Cycles" and eq. (3), p.9; δ_k, p.10; b_k, p.35; eq. (61) and eq. (62), p.36; L and m in Theorems 5.2, 5.3, p.36

import Mathlib
import Definitions.Def_AFIsingKS_Matching

open scoped Classical

namespace AFIsingKS.Supplement

/-- The sockets `V × [d]` of the configuration model, `V = Fin n`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9). -/
abbrev Socket (n d : ℕ) : Type := Fin n × Fin d

/-- The `k`-cycles `𝒞_k` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…),
Section 2.2 "Cycles", p.9): collections of `k` pairwise disjoint socket pairs
`{(u_t, i_t), (v_t, j_t)}` forming a length-`k` cycle after the clouds are contracted (`v_t = u_{t+1}`),
every cloud on it being visited exactly twice.

**Formalization Note.** A cycle is the finite set of its socket pairs (`Sym2` of sockets), so a cycle,
its rotations and its reversal are one object, and `|𝒞_k| = (n)_k d^k (d−1)^k / (2k)` (eq. (3)). It is the
image of the parametrisation `t ↦ {(v t, i t), (v (t+1), j (t+1))}` (indices mod `k`, `finRotate`) over
injective cloud sequences `v` and socket labels with `i t ≠ j t` (the two sockets used at the cloud `v t`
are distinct). `k = 1` gives the loops (two distinct sockets of one cloud), `k = 2` the double edges.
Only `k ≥ 1` is used. -/
noncomputable def cycles (n d k : ℕ) : Finset (Finset (Sym2 (Socket n d))) :=
  ((Finset.univ : Finset ((Fin k → Fin n) × (Fin k → Fin d) × (Fin k → Fin d))).filter
      (fun p => Function.Injective p.1 ∧ ∀ t, p.2.1 t ≠ p.2.2 t)).image
    (fun p => Finset.univ.image
      (fun t : Fin k => s((p.1 t, p.2.1 t), (p.1 (finRotate k t), p.2.2 (finRotate k t)))))

/-- The clouds a set of socket pairs meets (the vertices of the cycle). -/
noncomputable def clouds {n d : ℕ} (C : Finset (Sym2 (Socket n d))) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ e ∈ C, ∃ i : Fin d, (v, i) ∈ e)

/-- `|Γ| = Σ_{C ∈ Γ} |C| = Σ_k k · c_k(Γ)`, the total number of socket pairs of the cycles of `Γ`
(p.35). -/
def familySize {n d : ℕ} (Γ : Finset (Finset (Sym2 (Socket n d)))) : ℕ :=
  ∑ C ∈ Γ, C.card

/-- The good families `𝒢(≤ m) = ⋃_{m' ≤ m} 𝒢(m')` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598
(held version, sha256 2a07c158…), eq. (61), p.36): sets `Γ` of cycles of lengths `1, …, L` that consist of
vertex-disjoint cycles and have `|Γ| = Σ_k k c_k(Γ) ≤ m`.

**Formalization Note.** `Γ` is a `Finset` of cycles, so a cycle occurs at most once (as the page notes for
every `Γ ∈ 𝒢`). "Vertex-disjoint" means that two distinct cycles of `Γ` meet disjoint sets of clouds. The
empty family belongs to `𝒢(≤ m)` (it has `c(∅) = 0`). -/
noncomputable def goodFamilies (n d L m : ℕ) : Finset (Finset (Finset (Sym2 (Socket n d)))) :=
  ((Finset.Icc 1 L).biUnion (cycles n d)).powerset.filter
    (fun Γ => (∀ C ∈ Γ, ∀ C' ∈ Γ, C ≠ C' → Disjoint (clouds C) (clouds C')) ∧ familySize Γ ≤ m)

/-- The event `{Γ ⊆ M} = ⋀_{C ∈ Γ} {C ⊆ M}` (p.35): every socket pair of every cycle of `Γ` is matched
by `M`. A pair `e` is matched by `M` iff `e = {x, M x}` for some socket `x`. -/
def familyInMatching {n d : ℕ} (Γ : Finset (Finset (Sym2 (Socket n d)))) (M : Matching n d) : Prop :=
  ∀ C ∈ Γ, ∀ e ∈ C, ∃ x : Socket n d, e = s(x, M.1 x)

/-- `λ_k = (d−1)^k / (2k)` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version,
sha256 2a07c158…), eq. (3), p.9). -/
noncomputable def lam (d k : ℕ) : ℝ := ((d : ℝ) - 1) ^ k / (2 * k)

/-- `δ_k(β) = ((e^{−β} − 1)/(e^{−β} + 1))^k ∈ ℂ` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held
version, sha256 2a07c158…), Section 2.2, p.10).

**Formalization Note.** At `e^{−β} = −1` (`Im β ≡ π mod 2π`) Lean's division gives `0`; the statements of
this supplement only evaluate `δ_k` near the real segment `[0, β_KS]`. -/
noncomputable def deltaK (k : ℕ) (β : ℂ) : ℂ :=
  ((Complex.exp (-β) - 1) / (Complex.exp (-β) + 1)) ^ k

/-- `b_k = (1 + δ_k)^{−1} − 1` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version,
sha256 2a07c158…), Section 5, p.35).

**Formalization Note.** Lean's `0⁻¹ = 0` makes `b_k = −1` where `δ_k = −1`; near `[0, β_KS]` one has
`|δ_k| < 1`, where the formula is the page's. -/
noncomputable def bK (k : ℕ) (β : ℂ) : ℂ := (1 + deltaK k β)⁻¹ - 1

/-- The truncated reweighting factor (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version,
sha256 2a07c158…), eq. (62), p.36):
`A_{L,m}(β) = exp(Σ_{k=1}^L λ_k δ_k(β)) · Σ_{Γ ∈ 𝒢(≤ m)} 1[Γ ⊆ M] Π_{C ∈ Γ} b_{|C|}(β)`,
a function of the perfect matching `M` of `V × [d]` and of `β ∈ ℂ`.

**Formalization Note.** `|C|` is the number of socket pairs of `C`, i.e. its length `k`. This is the
truncated factor `A_{L,m}` of eq. (62), not the "ideal" `A_L` of p.35. -/
noncomputable def reweight {n d : ℕ} (L m : ℕ) (M : Matching n d) (β : ℂ) : ℂ :=
  Complex.exp (∑ k ∈ Finset.Icc 1 L, (lam d k : ℂ) * deltaK k β) *
    ∑ Γ ∈ goodFamilies n d L m,
      if familyInMatching Γ M then ∏ C ∈ Γ, bK C.card β else 0

/-- The cycle-length cutoff `L = log log N / log log log N`, `N = nd`, of Theorems 5.2 and 5.3
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.36), rounded down.

**Formalization Note.** The page requires `L ∈ ℕ` (p.36) and prints the real quotient. `L` is only used as
the upper limit of `k ∈ {1, …, L}`, so `⌊L⌋₊` selects exactly the same `k`. Logarithms are natural. For the
finitely many `N` where an iterated logarithm is `≤ 0`, Lean's conventions give some natural number. -/
noncomputable def cutoffL (n d : ℕ) : ℕ :=
  ⌊Real.log (Real.log ((n : ℝ) * d)) / Real.log (Real.log (Real.log ((n : ℝ) * d)))⌋₊

/-- The size cutoff `m = log N / (log log N)^2`, `N = nd`, of Theorems 5.2 and 5.3
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.36), rounded down.

**Formalization Note.** `m` is only used through `|Γ| ≤ m` with `|Γ| ∈ ℕ`, so `⌊m⌋₊` selects exactly the
same families. -/
noncomputable def cutoffM (n d : ℕ) : ℕ :=
  ⌊Real.log ((n : ℝ) * d) / Real.log (Real.log ((n : ℝ) * d)) ^ 2⌋₊

end AFIsingKS.Supplement


