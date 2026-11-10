-- Prove2me | Definitions.Def_TurnstileRank_TightBounds_HardInstance
-- name    : TurnstileRank_TightBounds_HardInstance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:07:21.005208+00:00
-- url     : https://prove2.me/theorems/e749dafe-443b-43c1-a18e-f67a814d326a
-- title:
--   The hard distribution, linear sketches with noise, signed ranks, digitwise information and digitwise variance (§4)
-- statement:
--   §4.1 fixes $\eta_0=2^{-10}$ and a power of two $k$ with $k^{-1}\le\eta_0/8$ (`KeyBase k`); $c_0=\frac{8}{\ln 2}\big(\frac1{48}-\eta_0\big)$ (printed p. 21). Strings $[k]^d$ are `Str d k = Fin d → Fin k`, digit positions $0$-based (the paper's $X[j]$ is `X ⟨j−1⟩`, its level $i$ is index $i-1$); `strVal` is the lexicographic integer value, most significant digit first, so $V<X$ means `strVal V < strVal X`.
--
--   * Definition 4.2: $X$ is uniform on $[k]^d$ and, independently given $X$, $V_i$ is uniform among the strings agreeing with $X$ before position $i$. Lean draws $X,W_1,\dots,W_d$ independent and uniform and sets $V_i=$ `splice X W_i i` (digits of $X$ before $i$, of $W_i$ from $i$ on): the same law.
--   * Definition 4.3: a linear sketch with noise (`NoisySketch`) is a discrete joint law of the public randomness $\rho$ and a noise $N\in G$, and an item map $A_\rho:[k]^d\to G$; $(\rho,N)$ is independent of $(X,V)$ (`jointLaw`). The state of the first $i$ items is $A_\rho(V_{1:i};N)=N+\sum_{t\le i}A_\rho(V_t)$ (`stateUpTo i`), and `state` is $A_\rho(V_{1:d};N)$.
--   * Definition 4.4: a sign function $\sigma_\rho:[k]^d\to\{-1,1\}$ (`IsSign σ`); $R=\sum_i\sigma_\rho(V_i)1\{V_i<X\}$ (`signedRank`), $B_i=1\{V_i[i]\le X[i]\}$ (`digitCmp`), $\tilde R=\sum_i\sigma_\rho(V_i)B_i$ (`digitRank`).
--   * Definition 4.6: $I_{i,j}=I(V_i[j];A_\rho(V_{1:d};N)\mid\rho,V_i[1:j-1],V_{i+1:d})$ (`digitInfo S i j`).
--   * Definition 4.13: $\mathrm{Var}_i=\mathrm{Var}\big(\sigma_\rho(V_i)B_i+E[\sum_{t<i}\sigma_\rho(V_t)B_t\mid\rho,X,A_\rho(V_{1:i-1};N)]\ \big|\ \rho,X,A_\rho(V_{1:i};N)\big)$ (`digitVar S σ i`), with $\rho$ in the conditioning as the paper's convention says (p. 16).
--   * `DecodingBound a₀ δ₀ c` is the statement of Theorem 4.5 for given constants: for every admissible $k$, every $d$, every linear sketch with noise, every sign function and every estimate $T(\rho,X,A_\rho(V_{1:d};N))$, if $P[|T-R|>a_0\sqrt d]\le\delta_0$ then $I(V_{1:d};A_\rho(V_{1:d};N)\mid\rho)\ge cd^2$.
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, §4.1–§4.3, printed pp. 13–17 (PDF 14–18): Definitions 4.2, 4.3, 4.4, 4.6, 4.13

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_Info

/-!
# The key-regime hard distribution, linear sketches with noise, signed ranks, digitwise
# information and digitwise variance (§4)

Hu, Jiang, Liu, Yu (2026), held STOC 2027 submission (SHA-256 4be42600…), §4.1–§4.3, printed
pp. 13–17 (PDF 14–18).

* §4.1 (p. 13): "we fix `η₀ = 2⁻¹⁰` and a sufficiently large power of two `k` with
  `k⁻¹ ≤ η₀/8`. … We will consider each of the first `k^d` integers in `[U]` as a string of length
  `d`, with each element in `[k]`. The mapping is simply by lexicographical order … We use `X[a : b]`
  to represent the `a`-th to `b`-th elements in the string, indexed starting from one, where the most
  significant digits come first."
* Definition 4.2 (Hard distribution): "Choose `X` uniformly from `[k]^d`. Given `X`, independently
  choose `V_i` uniformly among the strings agreeing with `X` in their first `i − 1` digits."
* Definition 4.3 (Linear sketch with noise): public randomness `ρ` independent of `(X, V_{1:d})`,
  a group `G_ρ`, a map `A_ρ : [k]^d → G_ρ`, a noise `N ∈ G_ρ` independent of `(X, V_{1:d})` given
  `ρ`, and the state `A_ρ(v_1, …, v_m; N) := N + Σ_t A_ρ(v_t)`.
* Definition 4.4: a sign function `σ_ρ : [k]^d → {−1, 1}`, `R := Σ_i σ_ρ(V_i) 1{V_i < X}`,
  `B_i := 1{V_i[i] ≤ X[i]}`, `R̃ := Σ_i σ_ρ(V_i) B_i`.
* Definition 4.6: `I_{i,j} := I(V_i[j] ; A_ρ(V_{1:d}; N) | ρ, V_i[1 : j − 1], V_{i+1:d})`, `i ≤ j`.
* Definition 4.13: `Var_i := Var(σ_ρ(V_i)B_i + E[Σ_{t<i} σ_ρ(V_t)B_t | X, A_ρ(V_{1:i−1}; N)] |
  X, A_ρ(V_{1:i}; N))`; "where not displayed explicitly, `ρ` is suppressed from conditioning"
  (p. 16), so `ρ` is part of every conditioning.

**Formalization Note.**
* Strings `[k]^d` are `Fin d → Fin k`; digit positions and item indices are `0`-based (`Fin d`):
  the paper's level `i` is `i.val + 1` and its digit `X[j]` is `X ⟨j − 1⟩`. The lexicographic
  embedding into the integers is `strVal`, most significant digit first, so `V_i < X` is
  `strVal (V i) < strVal X`.
* The hard instance is built from independent uniform `X` and `W_1, …, W_d` on `[k]^d`:
  `V_i` copies the digits of `X` before position `i` and the digits of `W_i` from position `i` on
  (`splice`). This is exactly the law of Definition 4.2.
* One group `G` for all seeds (a family `G_ρ` embeds in a product). The pair `(ρ, N)` has an
  arbitrary discrete joint law `μ`, and `(X, V)` is independent of it (`noisyLaw`); this is
  "ρ independent of `(X, V)`, `N` independent of `(X, V)` given `ρ`".
* An estimate `T` is any function of `(ρ, X, A_ρ(V_{1:d}; N))`.
* `KeyBase k`: `k` is a power of two with `k⁻¹ ≤ η₀/8`. `[NeZero k]` only makes the uniform law
  on `[k]^d` well defined (`KeyBase k` already forces `k ≥ 2^13`).
-/

noncomputable section

open scoped BigOperators Classical

namespace TurnstileRank.TightBounds

/-- `η₀ = 2⁻¹⁰` (§4.1). -/
def eta0 : ℝ := 1 / 2 ^ 10

/-- `c₀ = (8 / ln 2)(1/48 − η₀)` (proof of Theorem 4.15, printed p. 21). -/
def c0 : ℝ := 8 / Real.log 2 * (1 / 48 - eta0)

/-- The section's base: `k` is a power of two with `k⁻¹ ≤ η₀/8`. -/
def KeyBase (k : ℕ) : Prop := (∃ m : ℕ, k = 2 ^ m) ∧ (k : ℝ)⁻¹ ≤ eta0 / 8

/-- Strings of length `d` over `[k]`, most significant digit first. -/
abbrev Str (d k : ℕ) := Fin d → Fin k

/-- The integer represented by a string, in lexicographic order: `Σ_j v_j k^{d−1−j}`. -/
def strVal {d k : ℕ} (v : Str d k) : ℕ := ∑ j : Fin d, (v j : ℕ) * k ^ (d - 1 - j.val)

/-- The string that agrees with `x` before position `i` and with `w` from position `i` on. -/
def splice {d k : ℕ} (x w : Str d k) (i : Fin d) : Str d k := fun j => if j < i then x j else w j

/-- A draw of the hard instance: the query `X` and independent uniform strings `W_1, …, W_d`. -/
abbrev HardSample (d k : ℕ) := Str d k × (Fin d → Str d k)

/-- Definition 4.2: the hard distribution (uniform on `HardSample`). -/
def hardLaw (d k : ℕ) [NeZero k] : PMF (HardSample d k) := PMF.uniformOfFintype _

/-- The query `X`. -/
def HardSample.X {d k : ℕ} (h : HardSample d k) : Str d k := h.1

/-- The item `V_i`: uniform among the strings agreeing with `X` before position `i`. -/
def HardSample.V {d k : ℕ} (h : HardSample d k) (i : Fin d) : Str d k := splice h.1 (h.2 i) i

/-- Definition 4.3: a linear sketch with noise on `[k]^d`: the joint law of the public randomness
`ρ` and the noise `N`, and the item map `A_ρ`. -/
structure NoisySketch (d k : ℕ) (Ρ G : Type) [AddCommGroup G] where
  /-- The joint law of `(ρ, N)`. -/
  law : PMF (Ρ × G)
  /-- The item map `A_ρ : [k]^d → G`. -/
  item : Ρ → Str d k → G

/-- The sample space of §4: seed, noise and hard instance. -/
abbrev KeySample (d k : ℕ) (Ρ G : Type) := Ρ × G × HardSample d k

namespace NoisySketch

variable {d k : ℕ} {Ρ G : Type} [AddCommGroup G]

/-- The joint law of `(ρ, N, X, V)`: `(ρ, N) ∼ S.law` independent of the hard instance. -/
def jointLaw [NeZero k] (_S : NoisySketch d k Ρ G) : PMF (KeySample d k Ρ G) :=
  _S.law.bind fun pn => (hardLaw d k).map fun h => (pn.1, pn.2, h)

/-- `A_ρ(V_{1:i}; N) = N + Σ_{t ≤ i} A_ρ(V_t)` (the first `i` items, `i = 0, …, d`). -/
def stateUpTo (S : NoisySketch d k Ρ G) (i : ℕ) (ω : KeySample d k Ρ G) : G :=
  ω.2.1 + ∑ t ∈ Finset.univ.filter (fun t : Fin d => t.val < i), S.item ω.1 (ω.2.2.V t)

/-- The final state `A_ρ(V_{1:d}; N)`. -/
def state (S : NoisySketch d k Ρ G) (ω : KeySample d k Ρ G) : G := S.stateUpTo d ω

end NoisySketch

/-- A sign function: `σ_ρ(v) ∈ {−1, 1}`. -/
def IsSign {d k : ℕ} {Ρ : Type} (σ : Ρ → Str d k → ℝ) : Prop := ∀ ρ v, σ ρ v = 1 ∨ σ ρ v = -1

/-- The digit comparison `B_t = 1{V_t[t] ≤ X[t]}`. -/
def digitCmp {d k : ℕ} {Ρ G : Type} (t : Fin d) (ω : KeySample d k Ρ G) : ℝ :=
  if ω.2.2.V t t ≤ ω.2.2.X t then 1 else 0

/-- Definition 4.4: the signed rank `R = Σ_i σ_ρ(V_i) 1{V_i < X}`. -/
def signedRank {d k : ℕ} {Ρ G : Type} (σ : Ρ → Str d k → ℝ) (ω : KeySample d k Ρ G) : ℝ :=
  ∑ i : Fin d, σ ω.1 (ω.2.2.V i) * (if strVal (ω.2.2.V i) < strVal ω.2.2.X then 1 else 0)

/-- Definition 4.4: the digit approximation `R̃ = Σ_i σ_ρ(V_i) B_i`. -/
def digitRank {d k : ℕ} {Ρ G : Type} (σ : Ρ → Str d k → ℝ) (ω : KeySample d k Ρ G) : ℝ :=
  ∑ i : Fin d, σ ω.1 (ω.2.2.V i) * digitCmp i ω

/-- Definition 4.6: the digitwise information
`I_{i,j} = I(V_i[j] ; A_ρ(V_{1:d}; N) | ρ, V_i[1 : j − 1], V_{i+1:d})` (used for `i ≤ j`). -/
def digitInfo {d k : ℕ} {Ρ G : Type} [AddCommGroup G] [NeZero k] (S : NoisySketch d k Ρ G)
    (i j : Fin d) : ENNReal :=
  condMI S.jointLaw (fun ω => ω.2.2.V i j) S.state
    (fun ω => (ω.1, (fun m : {m : Fin d // m < j} => ω.2.2.V i m.val),
      (fun t : {t : Fin d // i < t} => ω.2.2.V t.val)))

/-- The partial digit sum `Σ_{t < i} σ_ρ(V_t) B_t` (the paper's `Σ_{t=1}^{i−1}`). -/
def digitPrefix {d k : ℕ} {Ρ G : Type} (σ : Ρ → Str d k → ℝ) (i : Fin d)
    (ω : KeySample d k Ρ G) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin d => t < i), σ ω.1 (ω.2.2.V t) * digitCmp t ω

/-- Definition 4.13: the digitwise variance
`Var_i = Var(σ_ρ(V_i)B_i + E[Σ_{t<i} σ_ρ(V_t)B_t | ρ, X, A_ρ(V_{1:i−1}; N)] | ρ, X, A_ρ(V_{1:i}; N))`. -/
def digitVar {d k : ℕ} {Ρ G : Type} [AddCommGroup G] [NeZero k] (S : NoisySketch d k Ρ G)
    (σ : Ρ → Str d k → ℝ) (i : Fin d) : ℝ :=
  condVar S.jointLaw
    (fun ω => σ ω.1 (ω.2.2.V i) * digitCmp i ω +
      condExp S.jointLaw (digitPrefix σ i) (fun ω' => (ω'.1, ω'.2.2.X, S.stateUpTo i.val ω')) ω)
    (fun ω => (ω.1, ω.2.2.X, S.stateUpTo (i.val + 1) ω))

/-- The decoding hypothesis (4.3) and conclusion (4.4) of Theorem 4.5 for given constants:
for every admissible base `k`, every `d`, every linear sketch with noise, every sign function and
every estimate `T` of `R` from `(ρ, X, A_ρ(V_{1:d}; N))`, if `P[|T − R| > a₀√d] ≤ δ₀` then
`I(V_{1:d} ; A_ρ(V_{1:d}; N) | ρ) ≥ c d²`. Theorem 4.5 asserts it for some `a₀, δ₀, c > 0`. -/
def DecodingBound (a0 δ0 c : ℝ) : Prop :=
  ∀ (k : ℕ) [NeZero k], KeyBase k → ∀ (d : ℕ) (Ρ G : Type) [AddCommGroup G]
    (S : NoisySketch d k Ρ G) (σ : Ρ → Str d k → ℝ), IsSign σ →
    ∀ T : Ρ → Str d k → G → ℝ,
      prob S.jointLaw {ω | a0 * Real.sqrt d < |T ω.1 ω.2.2.X (S.state ω) - signedRank σ ω|} ≤ δ0 →
      ENNReal.ofReal (c * (d : ℝ) ^ 2) ≤
        condMI S.jointLaw (fun ω => fun i => ω.2.2.V i) S.state (fun ω => ω.1)

end TurnstileRank.TightBounds


