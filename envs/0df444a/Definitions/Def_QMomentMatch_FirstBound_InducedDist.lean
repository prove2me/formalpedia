-- Prove2me | Definitions.Def_QMomentMatch_FirstBound_InducedDist
-- name    : QMomentMatch_FirstBound_InducedDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T19:00:00.683866+00:00
-- url     : https://prove2.me/theorems/4ada1e94-1e66-47a2-8c86-742ed15e1329
-- title:
--   Definition 2.1 — frequency vectors, $\mathcal D_{\mathbf c}$, the induced input distribution $\Pi_N$, acceptance probabilities
-- statement:
--   Fix an integer $N\ge1$. Inputs are functions $f:[N]\to[N]$, queried by a quantum algorithm through the standard oracle $O_f:|i,y\rangle\mapsto|i,y+f(i)\bmod N\rangle$.
--
--   1. The **frequency vector** of $f$ is $\mathbf c(f)=(|f^{-1}(1)|,\dots,|f^{-1}(N)|)$. A vector $\mathbf c\in\mathbb Z_{\ge0}^N$ is **feasible** if $\sum_j c_j=N$.
--   2. For a feasible $\mathbf c$, $\mathcal D_{\mathbf c}$ is the **uniform distribution on the functions whose frequency vector is a permutation of $\mathbf c$**.
--   3. **Definition 2.1 (induced input distribution).** Let $X$ be positive frequency statistics supported on $[A]$ and $Z$ its mean-one statistics, with law $\pi$ on $S=\{0\}\cup[A]$. Let $m=\lfloor N/2\rfloor$. Draw $z=(z_1,\dots,z_m)$ i.i.d. from $\pi$ and put $z=\sum_i z_i$. If $z\le N$, let $\mathbf c(z)$ consist of the non-zero entries of $z$, then $N-z$ entries equal to $1$, then zeros up to length $N$; if $z>N$, let $\mathbf c(z)=(1,\dots,1)$. Finally draw $f\sim\mathcal D_{\mathbf c(z)}$. The law of $f$ is $\Pi_N$:
--   $$\Pi_N(f)=\sum_{z\in S^m}\Big(\prod_{i=1}^m\pi(z_i)\Big)\,\mathcal D_{\mathbf c(z)}(f).$$
--   4. For a $T$-query algorithm $\mathcal A$ (input-independent start state and unitaries $U_0,\dots,U_T$ on the query register and a finite workspace, $T$ oracle calls, final computational-basis measurement post-processed by a Boolean map), $\Pr[\mathcal A^f=1]$ is its probability of outputting $1$ on input $f$, and for a law $\mu$ on inputs $\Pr_{f\sim\mu}[\mathcal A^f=1]=\sum_f\mu(f)\Pr[\mathcal A^f=1]$.
--   5. For multiplicities $z$, $h(z)=\Pr_{f\sim\mathcal D_{\mathbf c(z)}}[\mathcal A^f=1]$ (eq. (5), §3.3).
--
--   These are the input distributions that Theorem 2.5 compares, and the symmetrized acceptance probability $h$ that its proof analyses.
--
--   **Formalization Note** The domain $[N]$ is `Fin N` (0-based) and an output label $j\in[N]$ is the residue $j \bmod N$ in `ZMod N`, so the standard oracle is exactly `QAlgorithms.xorOracle f` from the published definition `QAlgorithms_Defs_Query`. Because $\mathcal D_{\mathbf c}$ depends on $\mathbf c$ only up to permutation, a frequency vector is represented by the multiset of its entries. $\mathcal D_{\mathbf c}$ is given by its mass function, $1/|\{f : \mathbf c(f)\sim\mathbf c\}|$ on that set and $0$ elsewhere; for a feasible $\mathbf c$ the set is nonempty, and $\mathbf c(z)$ is always feasible.
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), §2.1 pp. 11–12, Definition 2.1 p. 12, Remark 2.2 eq. (5) p. 12, §2.2 p. 13, §3.3 p. 21

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QMomentMatch_FirstBound_Basic

/-!
# Frequency vectors, `D_c`, the induced input distribution `Π_N`, acceptance probabilities

Kayal, Magniez, Sen, Szabó, STOC 2027 submission #564, §2.1 (pp. 11–12), Definition 2.1 (p. 12),
§3.3 (p. 21).

Conventions. Inputs `f : [N] → [N]` are `f : Fin N → ZMod N`: the domain `[N]` is `Fin N`
(0-based) and an output label `j ∈ [N]` is the residue `j mod N`, so the standard query
`|i, y⟩ ↦ |i, y + f(i) mod N⟩` is `QAlgorithms.xorOracle f`. A frequency vector is used only up
to permutation, so it is represented by the multiset of its entries.
-/

namespace QMomentMatch.FirstBound

open QAlgorithms

/-- p. 11: the frequency vector `c(f) = (|f⁻¹(1)|, …, |f⁻¹(N)|)`, as the multiset of its entries
(one entry per output label). -/
def freqMultiset {N : ℕ} [NeZero N] (f : Fin N → ZMod N) : Multiset ℕ :=
  (Finset.univ : Finset (ZMod N)).val.map fun j => (Finset.univ.filter fun i => f i = j).card

/-- The multiset of entries of a vector `c ∈ ℕ^N`. -/
def vecMultiset {N : ℕ} (c : Fin N → ℕ) : Multiset ℕ :=
  (Finset.univ : Finset (Fin N)).val.map c

/-- p. 11: a vector `c ∈ ℤ_{≥0}^N` is feasible if `∑_j c_j = N`. -/
def IsFeasible {N : ℕ} (c : Fin N → ℕ) : Prop :=
  ∑ j, c j = N

/-- The functions `f : [N] → [N]` whose frequency vector is a permutation of `c`. -/
def funsWithFreq (N : ℕ) [NeZero N] (c : Multiset ℕ) : Finset (Fin N → ZMod N) :=
  Finset.univ.filter fun f => freqMultiset f = c

/-- p. 12: `D_c`, the uniform distribution on the functions whose frequency vector is a
permutation of `c`; the mass it gives to `f`. (For a feasible `c` the support is nonempty; the
value `0` on an empty support is never used for a feasible `c`.) -/
noncomputable def dcMass {N : ℕ} [NeZero N] (c : Multiset ℕ) (f : Fin N → ZMod N) : ℝ :=
  if f ∈ funsWithFreq N c then 1 / ((funsWithFreq N c).card : ℝ) else 0

/-- Definition 2.1, step 2 (p. 12): from multiplicities `z = (z_1, …, z_m)` with sum `z`, if
`z ≤ N` take the non-zero entries of `z`, add `N − z` entries equal to `1`, and pad with zeros to
length `N`; if `z > N`, take `c = (1, …, 1)`. Returned as the multiset of entries of `c(z)`. -/
def drawsFreq (N : ℕ) {A m : ℕ} (z : Fin m → Fin (A + 1)) : Multiset ℕ :=
  let zs := ∑ i, (z i : ℕ)
  let nz := ((Finset.univ : Finset (Fin m)).val.map fun i => (z i : ℕ)).filter (· ≠ 0)
  if zs ≤ N then nz + Multiset.replicate (N - zs) 1 + Multiset.replicate (zs - Multiset.card nz) 0
  else Multiset.replicate N 1

/-- Definition 2.1 (p. 12): the induced input distribution `Π_N` of positive frequency statistics
`X`: draw `m = ⌊N/2⌋` i.i.d. multiplicities `z` from the mean-one statistics `Z` of `X`, form
`c(z)` (step 2), and draw `f ∼ D_{c(z)}`. The mass `Π_N(f) = ∑_{z ∈ S^m} π^{⊗m}(z) D_{c(z)}(f)`. -/
noncomputable def inducedDist {A : ℕ} (X : Fin (A + 1) → ℝ) (N : ℕ) [NeZero N]
    (f : Fin N → ZMod N) : ℝ :=
  prodExp (meanOne X) fun z : Fin (N / 2) → Fin (A + 1) => dcMass (drawsFreq N z) f

/-- The probability that the `T`-query algorithm `alg`, with standard query access to `f` and
final computational-basis measurement post-processed by `out`, outputs `1` (`true`). -/
noncomputable def accProb {N : ℕ} [NeZero N] {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (alg : QueryAlg (Fin N) (ZMod N) W T) (out : (Fin N × ZMod N) × W → Bool)
    (f : Fin N → ZMod N) : ℝ :=
  alg.outputProb (xorOracle f) out true

/-- `Pr_{f ∼ μ}[A^f = 1] = ∑_f μ(f) Pr[A^f = 1]`, including the draw of `f` from the law `μ` and
the algorithm's measurement. -/
noncomputable def probAccept {N : ℕ} [NeZero N] {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (μ : (Fin N → ZMod N) → ℝ) (alg : QueryAlg (Fin N) (ZMod N) W T)
    (out : (Fin N × ZMod N) × W → Bool) : ℝ :=
  ∑ f, μ f * accProb alg out f

/-- p. 12 (eq. (5)) and p. 21: `h(z) = Pr_{f ∼ D_{c(z)}}[A^f = 1]` for multiplicities `z`. -/
noncomputable def hAcc {N : ℕ} [NeZero N] {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (alg : QueryAlg (Fin N) (ZMod N) W T) (out : (Fin N × ZMod N) × W → Bool)
    {A m : ℕ} (z : Fin m → Fin (A + 1)) : ℝ :=
  probAccept (dcMass (drawsFreq N z)) alg out

end QMomentMatch.FirstBound


