-- Prove2me | Definitions.Def_CommitOpen_Benign_Model
-- name    : CommitOpen_Benign_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:04.1261+00:00
-- url     : https://prove2.me/theorems/bbeac830-0e57-466a-a902-f428b5448f2d
-- title:
--   §2, §4.1, §4.3, pp. 3–11 — BB84 kets, measurement statistics, min-/max-entropy, Hamming distances, the test distribution, B_test, cq states, trace distance, negligible functions
-- statement:
--   This file fixes the objects of the commit-and-open analysis of Damgård, Fehr, Lunemann, Salvail and Schaffner.
--
--   **Qubits and BB84 states (§2, p. 3).** A bit is an element of $\{0,1\}$ and a basis is an element of $\{+,\times\}$. The computational basis is $\{|0\rangle,|1\rangle\}$, and the diagonal basis is $|0\rangle_\times=(|0\rangle+|1\rangle)/\sqrt2$, $|1\rangle_\times=(|0\rangle-|1\rangle)/\sqrt2$. For strings $x\in\{0,1\}^m$ and $\theta\in\{+,\times\}^m$,
--   $$|x\rangle_\theta=|x_1\rangle_{\theta_1}\otimes\cdots\otimes|x_m\rangle_{\theta_m}\in\mathbb C^{\{0,1\}^m}.$$
--
--   **Measuring Alice's register.** Alice's register $A$ is $\mathbb C^{\{0,1\}^m}$ and Bob's register $E$ is $\mathbb C^{E}$ for a finite set $E$. For a joint vector $|\varphi\rangle\in\mathcal H_A\otimes\mathcal H_E$ and a vector $|u\rangle$ of $\mathcal H_A$, the vector $(\langle u|\otimes 1_E)|\varphi\rangle$ of $\mathcal H_E$ has squared norm $\|(\langle u|\otimes1)|\varphi\rangle\|^2$, the Born-rule probability of outcome $u$. Measuring all of $A$ position-wise in bases $\theta$ yields outcome $x$ with probability $P_\theta(x)=\|(\langle x|_\theta\otimes1)|\varphi\rangle\|^2$.
--
--   **Lemma 2.3's objects (p. 3).** Given an orthonormal basis $\{|i\rangle\}_{i\in I}$ of $\mathcal H_A$, a finite $J\subseteq I$, coefficients $\alpha_i$ and vectors $|\varphi^i_E\rangle$, the superposition is $|\varphi_{AE}\rangle=\sum_{i\in J}\alpha_i|i\rangle|\varphi^i_E\rangle$. The mixture $\tilde\rho_{AE}=\sum_{i\in J}|\alpha_i|^2|i\rangle\langle i|\otimes|\varphi^i_E\rangle\langle\varphi^i_E|$ gives outcome $w$ with probability $\sum_{i\in J}|\alpha_i|^2|\langle w|i\rangle|^2$ (for unit $\varphi^i_E$). The reduced state is $\rho_E=\operatorname{tr}_A|\varphi_{AE}\rangle\langle\varphi_{AE}|$, with entries $(\rho_E)_{ee'}=\sum_a\varphi(a,e)\overline{\varphi(a,e')}$.
--
--   **Entropies (Definitions 2.1, 2.2).** For a distribution $P$ on a finite set, $H_\infty=-\log_2\max_x P(x)$. For a matrix $\rho$, $H_0(\rho)=\log_2\operatorname{rank}\rho$. For $P$ on $\{0,1\}^m$, $I\subseteq\{1,\dots,m\}$ and $x$, the conditional min-entropy $H_\infty(X|_I\mid X|_{\bar I}=x|_{\bar I})$ is the min-entropy of $y\mapsto P(y)/P(X|_{\bar I}=x|_{\bar I})$ over the strings $y$ with $y|_{\bar I}=x|_{\bar I}$. The binary entropy in bits is $h(\mu)=-(\mu\log_2\mu+(1-\mu)\log_2(1-\mu))$.
--
--   **Hamming distances (pp. 3, 10).** $d_H(x|_S,y|_S)=|\{i\in S:x_i\ne y_i\}|$ and $r_H(x|_S,y|_S)=d_H(x|_S,y|_S)/|S|$.
--
--   **The test (p. 10).** A test is a pair $(T,T')$ with $|T|=k$ and $T'\subseteq T$. $T$ is uniform among the $k$-subsets of the $m$ positions, and $T'=\{i\in T:\theta_i=\hat\theta_i\}$ for uniform $\theta$ is a uniform subset of $T$, so
--   $$P_{Test}(T,T')=\frac{1}{\binom mk\,2^k}.$$
--   For $\varepsilon>0$ and Bob's committed $\hat x$,
--   $$B_{test}=\{x\in\{0,1\}^m: r_H(x|_{\bar T},\hat x|_{\bar T})\le r_H(x|_{T'},\hat x|_{T'})+\varepsilon\}.$$
--
--   **cq states and trace distance.** For a family of vectors $\psi_{test}$, the cq state is $\sum_{test}P_{Test}(test)|test\rangle\langle test|\otimes|\psi_{test}\rangle\langle\psi_{test}|$, a block-diagonal matrix. The trace distance is $\delta(\rho,\sigma)=\tfrac12\operatorname{tr}|\rho-\sigma|$. A function $\nu:\mathbb N\to\mathbb R$ is **negligible** if for every $c$, $|\nu(m)|\le m^{-c}$ for all sufficiently large $m$.
--
--   **Alice's measurements in Fig. 4.** In Step 2 Alice measures the positions in $T$ in Bob's bases $\hat\theta|_T$; in Step 3 she measures $\bar T$ in her bases $\theta|_{\bar T}$. The basis string $\theta^*$ equals $\hat\theta$ on $T$ and $\theta$ on $\bar T$. Bob's state after Alice saw $x|_T$ is $\sum_{y:\,y|_T=x|_T}|a_y\rangle\langle a_y|$ with $|a_y\rangle=(\langle y|_{\theta^*}\otimes1)|\varphi\rangle$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Bits are `Bool`; bases are `Bool` with `false` = $+$ and `true` = $\times$. Positions are `Fin m`, 0-based (the paper's position $i$ is `i - 1`). $\log$ is $\log_2$ (`Real.logb 2`), and $h$ is Mathlib's `Real.binEntropy` (nats) divided by $\ln 2$. The trace norm is the published `WildeQIT.traceNorm` ($\operatorname{tr}\sqrt{M^\dagger M}$, which equals the paper's $\operatorname{tr}\sqrt{MM^\dagger}$). $r_H$ on the empty set is $0$ (Lean's $0/0$); this happens only for $T'=\emptyset$. The conditional min-entropy divides by the probability of the conditioning event; every statement using it assumes that probability is positive. Alice's two measurements (Steps 2 and 3) are encoded as a single measurement of all of $A$ in $\theta^*$, which has the same joint outcome law since the measurements act on disjoint registers. Bob's state is kept unnormalized; its rank, and hence $H_0$, is unaffected. For a pure joint state it is also the pointwise purification $\rho_{ER}$ of Definition 4.1. `bb84Ket` agrees with the platform's `Claimed50.P31.bb84Vector`, which is not imported.
-- source:
--   Damgård, Fehr, Lunemann, Salvail & Schaffner, Improving the Security of Quantum Protocols via Commit-and-Open, arXiv:0902.3918v4, pp. 3–11, §2 (Definitions 2.1, 2.2, Lemma 2.3), Definition 4.1, Fig. 4, §4.3 (p. 10, Lemma 4.3, p. 11)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm

namespace CommitOpen.Benign

open Matrix

/-- §2, p. 3: the one-qubit BB84 ket `|b⟩_θ`, written in the computational basis
`{|0⟩, |1⟩} = {false, true}` and evaluated at the computational basis vector `z`.
`θ = false` is the `+`-basis (`|b⟩_+ = |b⟩`), `θ = true` is the `×`-basis
(`|0⟩_× = (|0⟩ + |1⟩)/√2`, `|1⟩_× = (|0⟩ − |1⟩)/√2`). -/
noncomputable def ketBit (θ b z : Bool) : ℂ :=
  if θ then (if b && z then -((Real.sqrt 2 : ℂ)⁻¹) else (Real.sqrt 2 : ℂ)⁻¹)
  else (if z = b then 1 else 0)

/-- §2, p. 3: `|x⟩_θ = |x₁⟩_θ₁ ⊗ ⋯ ⊗ |x_m⟩_θ_m`, a vector of `ℂ^{{0,1}^m}`.
Positions are `Fin m` (0-based). -/
noncomputable def bb84Ket {m : ℕ} (θ x : Fin m → Bool) : EuclideanSpace ℂ (Fin m → Bool) :=
  WithLp.toLp 2 fun z => ∏ i, ketBit (θ i) (x i) (z i)

/-- `(⟨u| ⊗ 1_E)|φ⟩`, the (unnormalized) vector of register `E` left when register `A` of the
joint vector `φ ∈ H_A ⊗ H_E` is projected onto `u`. -/
noncomputable def ampAlong {ι E : Type} [Fintype ι] (u : EuclideanSpace ℂ ι)
    (φ : EuclideanSpace ℂ (ι × E)) : E → ℂ :=
  fun e => ∑ a, star (u a) * φ (a, e)

/-- Born rule: the probability `‖(⟨u| ⊗ 1_E)|φ⟩‖²` of the outcome `u` when register `A` of
`φ` is measured in an orthonormal basis containing `u`. -/
noncomputable def measProb {ι E : Type} [Fintype ι] [Fintype E] (u : EuclideanSpace ℂ ι)
    (φ : EuclideanSpace ℂ (ι × E)) : ℝ :=
  ∑ e, ‖ampAlong u φ e‖ ^ 2

/-- `(⟨x|_θ ⊗ 1_E)|φ⟩`, a vector of `E`. -/
noncomputable def amp {m : ℕ} {E : Type} (θ x : Fin m → Bool)
    (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)) : E → ℂ :=
  ampAlong (bb84Ket θ x) φ

/-- Probability of the outcome string `x` when all of register `A` of `φ` is measured
position-wise in the bases `θ`. -/
noncomputable def outcomeProb {m : ℕ} {E : Type} [Fintype E] (θ : Fin m → Bool)
    (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (x : Fin m → Bool) : ℝ :=
  measProb (bb84Ket θ x) φ

/-- Lemma 2.3, p. 3: the vector `|φ_AE⟩ = Σ_{i∈J} α_i |i⟩|φ^i_E⟩` built from a basis `b` of
`H_A`, a finite index set `J`, coefficients `α` and vectors `φ^i_E` of `H_E`. -/
noncomputable def superposition {ι I E : Type} [Fintype ι] [Fintype I]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (φE : I → EuclideanSpace ℂ E) : EuclideanSpace ℂ (ι × E) :=
  WithLp.toLp 2 fun p => ∑ i ∈ J, α i * b i p.1 * φE i p.2

/-- Lemma 2.3 (1), p. 3: the probability of the outcome `u` when register `A` of the mixture
`ρ̃_AE = Σ_{i∈J} |α_i|² |i⟩⟨i| ⊗ |φ^i_E⟩⟨φ^i_E|` (unit `φ^i_E`) is measured in a basis
containing `u`: `Σ_{i∈J} |α_i|² |⟨u|i⟩|²`. -/
noncomputable def mixtureProb {ι I : Type} [Fintype ι] [Fintype I]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (u : EuclideanSpace ℂ ι) : ℝ :=
  ∑ i ∈ J, ‖α i‖ ^ 2 * ‖inner ℂ u (b i)‖ ^ 2

/-- The reduced density matrix `ρ_E = tr_A(|φ_AE⟩⟨φ_AE|)`:
`(ρ_E)_{e e'} = Σ_a φ(a, e) · conj φ(a, e')`. -/
noncomputable def reducedE {ι E : Type} [Fintype ι] (φ : EuclideanSpace ℂ (ι × E)) :
    Matrix E E ℂ :=
  Matrix.of fun e e' => ∑ a, φ (a, e) * star (φ (a, e'))

/-- Definition 2.1, p. 3: `H∞(X) = −log₂ max_x P_X(x)`. -/
noncomputable def minEntropy {α : Type} [Fintype α] [Nonempty α] (P : α → ℝ) : ℝ :=
  -Real.logb 2 (Finset.univ.sup' Finset.univ_nonempty P)

/-- The strings `y ∈ {0,1}^m` that agree with `x` on every position of `S`. -/
def agreeOn {m : ℕ} (S : Finset (Fin m)) (x : Fin m → Bool) : Finset (Fin m → Bool) :=
  Finset.univ.filter fun y => ∀ i ∈ S, y i = x i

theorem self_mem_agreeOn {m : ℕ} (S : Finset (Fin m)) (x : Fin m → Bool) : x ∈ agreeOn S x := by
  simp [agreeOn]

/-- `H∞(X|_I | X|_Ī = x|_Ī)` for a distribution `P` of `X ∈ {0,1}^m`: the min-entropy of the
conditional law `P(y) / P(X|_Ī = x|_Ī)` over the strings `y` that agree with `x` off `I`.
(When the conditioning event has probability `0` the quotient is Lean's `0/0 = 0`; every
statement using it assumes positive probability.) -/
noncomputable def condMinEntropy {m : ℕ} (P : (Fin m → Bool) → ℝ) (I : Finset (Fin m))
    (x : Fin m → Bool) : ℝ :=
  -Real.logb 2 ((agreeOn Iᶜ x).sup' ⟨x, self_mem_agreeOn Iᶜ x⟩
    fun y => P y / ∑ y' ∈ agreeOn Iᶜ x, P y')

/-- Definition 2.2, p. 3: `H₀(ρ) = log₂ rank ρ`. -/
noncomputable def maxEntropy {E : Type} [Fintype E] (ρ : Matrix E E ℂ) : ℝ :=
  Real.logb 2 (ρ.rank : ℝ)

/-- p. 11: the binary entropy in bits, `h(μ) = −(μ log₂ μ + (1 − μ) log₂ (1 − μ))`
(Mathlib's `Real.binEntropy` is in nats). -/
noncomputable def binEntropy2 (μ : ℝ) : ℝ :=
  Real.binEntropy μ / Real.log 2

/-- §2, p. 3: the Hamming distance of `x` and `y` on the positions `S`,
`d_H(x|_S, y|_S) = |{i ∈ S : x_i ≠ y_i}|`. -/
def hammingOn {m : ℕ} (S : Finset (Fin m)) (x y : Fin m → Bool) : ℕ :=
  (S.filter fun i => x i ≠ y i).card

/-- p. 10: the relative Hamming distance `r_H(x|_S, y|_S) = d_H(x|_S, y|_S)/|S|`
(equal to `0` when `S = ∅`, Lean's `0/0`). -/
noncomputable def relHamming {m : ℕ} (S : Finset (Fin m)) (x y : Fin m → Bool) : ℝ :=
  (hammingOn S x y : ℝ) / S.card

/-- p. 10: a value `test = (T, T′)` of the random variable `Test`: a subset `T` of size `k`
(the paper's `αm`) and a subset `T′ ⊆ T`. -/
abbrev Test (m k : ℕ) := {p : Finset (Fin m) × Finset (Fin m) // p.1.card = k ∧ p.2 ⊆ p.1}

/-- p. 10: `P_Test(T, T′)`: `T` is uniform among the `k`-subsets of `{1,…,m}` and, for a fixed
`θ̂` and uniform `θ`, `T′ = {i ∈ T : θ_i = θ̂_i}` is a uniform subset of `T`. -/
noncomputable def testProb (m k : ℕ) (_ : Test m k) : ℝ :=
  ((m.choose k : ℝ) * 2 ^ k)⁻¹

/-- Lemma 4.3, p. 11: `B_test = {x ∈ {0,1}^m : r_H(x|_T̄, x̂|_T̄) ≤ r_H(x|_T′, x̂|_T′) + ε}`. -/
noncomputable def goodSet {m k : ℕ} (ε : ℝ) (xhat : Fin m → Bool) (t : Test m k) :
    Finset (Fin m → Bool) :=
  Finset.univ.filter fun x => relHamming t.1.1ᶜ x xhat ≤ relHamming t.1.2 x xhat + ε

/-- The pure-state density matrix `|ψ⟩⟨ψ|`. -/
noncomputable def pureState {ι : Type} (ψ : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.of fun a b => ψ a * star (ψ b)

/-- p. 10–11: the cq state `Σ_test P_Test(test) |test⟩⟨test| ⊗ |ψ_test⟩⟨ψ_test|`, as a
block-diagonal matrix indexed by `Test m k × ι`. -/
noncomputable def cqState {m k : ℕ} {ι : Type} (ψ : Test m k → EuclideanSpace ℂ ι) :
    Matrix (Test m k × ι) (Test m k × ι) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (testProb m k p.1 : ℂ) * pureState (ψ p.1) p.2 q.2 else 0

/-- §2, p. 3: the trace distance `δ(ρ, σ) = ½ tr|ρ − σ|`. -/
noncomputable def traceDistance {ι : Type} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ) : ℝ :=
  1 / 2 * WildeQIT.traceNorm (ρ - σ)

/-- A function `ν : ℕ → ℝ` is negligible: for every `c`, `|ν(m)| ≤ m^{-c}` for all large `m`
(standard meaning; the paper does not define it, p. 3). -/
def Negligible (ν : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, ∀ m ≥ N, |ν m| ≤ ((m : ℝ) ^ c)⁻¹

/-- Fig. 4: the bases `θ*` of Alice's two measurements — `θ̂` on the test set `T` (Step 2) and
`θ` on `T̄` (Step 3). -/
def mixBasis {m : ℕ} (T : Finset (Fin m)) (θhat θ : Fin m → Bool) : Fin m → Bool :=
  fun i => if i ∈ T then θhat i else θ i

/-- Bob's (unnormalized) state after Alice measured the positions `T` (in `θ*|_T`) and observed
`x|_T`: `Σ_{y : y|_T = x|_T} |a_y⟩⟨a_y|` with `a_y = (⟨y|_{θ*} ⊗ 1_E)|φ⟩`. It is the
unnormalized `tr_A` of the collapsed state, and for a pure `φ` also the pointwise purification
`ρ_ER` of Bob's state with respect to the outcome on `T̄`. -/
noncomputable def bobState {m : ℕ} {E : Type} (θstar : Fin m → Bool)
    (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (T : Finset (Fin m)) (x : Fin m → Bool) :
    Matrix E E ℂ :=
  ∑ y ∈ agreeOn T x, Matrix.vecMulVec (amp θstar y φ) (star (amp θstar y φ))

end CommitOpen.Benign


