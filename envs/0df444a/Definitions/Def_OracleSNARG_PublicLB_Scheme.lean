-- Prove2me | Definitions.Def_OracleSNARG_PublicLB_Scheme
-- name    : OracleSNARG_PublicLB_Scheme
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:46:37.668558+00:00
-- url     : https://prove2.me/theorems/2380d884-9e5f-4451-bebb-dafeab79beb7
-- title:
--   SNARGs with deterministic public verification for the majority computation; adaptive completeness and adaptive soundness (Definitions 9, 17); $o(\cdot)$ and polynomial bounds
-- statement:
--   Fix length functions $n,N:\mathbb N\to\mathbb N$ of the security parameter $\lambda$. A **scheme** $S=(\mathrm{Gen},P,V)$ consists of:
--   - $\mathrm{Gen}(1^\lambda)$: a probability distribution on bit strings $\mathrm{crs}$ for each $\lambda$. It gets no oracle.
--   - $P_\lambda$: the honest prover, a randomized oracle circuit. On inputs $[\mathrm{crs},x]$, its output $0$ is the proof $\pi$.
--   - $V_\lambda(\mathrm{crs},x,\pi)$: the verifier, a deterministic oracle procedure returning the accept bit. It has no private key and no coins.
--
--   No length bound is imposed on $\pi$.
--
--   **Adaptive completeness.** For every oracle $O$ and every polynomial-size randomized oracle algorithm $A$, there is a negligible $\nu$ with, for every $\lambda$,
--   $$\Pr_{\mathrm{crs}\leftarrow\mathrm{Gen}(1^\lambda),\ x\leftarrow A^O_\lambda(\mathrm{crs}),\ \pi\leftarrow P^O_\lambda(\mathrm{crs},x)}\big[\,|x|=n(\lambda)\ \wedge\ C^O(x)=1\ \wedge\ V^O_\lambda(\mathrm{crs},x,\pi)=0\,\big]\le\nu(\lambda).$$
--
--   **Adaptive soundness** (for a robustness parameter $\varepsilon$). For every oracle $O$ and every polynomial-size randomized oracle adversary $\mathrm{Adv}$, with outputs $x$ and $\pi^*$, there is a negligible $\mu$ with, for every $\lambda$,
--   $$\Pr_{\mathrm{crs}\leftarrow\mathrm{Gen}(1^\lambda),\ (x,\pi^*)\leftarrow \mathrm{Adv}^O_\lambda(\mathrm{crs})}\big[\,|x|=n(\lambda)\ \wedge\ C^O(x)=0\ \wedge\ C^O\text{ is }\varepsilon\text{-robust on }x\ \wedge\ V^O_\lambda(\mathrm{crs},x,\pi^*)=1\,\big]\le\mu(\lambda).$$
--
--   Here $C^O$ is the majority computation with $N(\lambda)$ oracle calls. A function is **negligible** if it is eventually at most $1/p(\lambda)$ for every positive polynomial $p$ (the published `OWFLocalDesc.Negligible`).
--
--   The asymptotic conditions are as follows.
--   - $f$ is **polynomially bounded** if $f(\lambda)\le p(\lambda)$ for a polynomial $p$ and every $\lambda$.
--   - $f=o(g)$ if for every real $c>0$, $f(\lambda)\le c\,g(\lambda)$ for all sufficiently large $\lambda$.
--   - $|\mathrm{crs}|=o(n)$ if for every $c>0$, for all sufficiently large $\lambda$, every $\mathrm{crs}$ in the support of $\mathrm{Gen}(1^\lambda)$ has length at most $c\,n(\lambda)$.
--
--   **Formalization Note.**
--   - The oracle in both properties is one function $O$ for all $\lambda$, fixed independently of setup (Definition 17).
--   - Gen and $V$ carry no efficiency bound in this definition; only the prover is a circuit.
--   - The non-adaptive completeness clause of Definition 17 is implied by the adaptive one (constant choosers are polynomial-size), so it is not repeated.
-- source:
--   Goldwasser, Kalai, Incrementally Verifiable Oracle Aided Computation, STOC 2027 submission (manuscript sha256 cc66f0af…), p. 13, Definition 9; p. 17, §4.1 and Definition 17; p. 24, Theorem 22 (|crs| = o(n), o(q) queries)

import Mathlib
import Definitions.Def_OWFLocalDesc_Negligible
import Definitions.Def_OracleSNARG_PublicLB_Majority
import Definitions.Def_OracleSNARG_PublicLB_Algorithms

set_option autoImplicit false

open Classical

namespace OracleSNARG.PublicLB

/-- **Polynomially bounded** function of the security parameter: `f(λ) ≤ p(λ)` for a polynomial
`p` and every `λ`. -/
def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ lam : ℕ, f lam ≤ p.eval lam

/-- **`f = o(g)`** as functions of `λ`: for every real `c > 0`, `f(λ) ≤ c · g(λ)` for all
sufficiently large `λ`. -/
def LittleO (f g : ℕ → ℕ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ lam in Filter.atTop, (f lam : ℝ) ≤ c * (g lam : ℝ)

/-- **A SNARG with deterministic public verification** for the majority computation
(§3.2, Definition 9, p. 13; §4.1, p. 17, with no private verification key):
* `gen λ` — the setup `Gen(1^λ)`: a distribution on bit strings `crs`; it gets no oracle;
* `prover λ` — the honest prover `P^O(crs, x)`: a randomized oracle circuit with inputs
  `[crs, x]` whose output `0` is the proof `π`;
* `verifier λ crs x π` — the verifier `V^O(crs, x, π)`: a deterministic oracle procedure
  (no coins, no private key) returning the accept bit.
No bound on the length of `π`. -/
structure Scheme : Type where
  gen : ℕ → PMF (List Bool)
  prover : ℕ → RCircuit
  verifier : ℕ → List Bool → List Bool → List Bool → QTree Bool

/-- **`|crs| = o(n)`**: for every real `c > 0`, for all sufficiently large `λ`, every `crs` in the
support of `Gen(1^λ)` has length at most `c · n(λ)`. -/
def CrsLittleO (n : ℕ → ℕ) (S : Scheme) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ lam in Filter.atTop,
    ∀ crs ∈ (S.gen lam).support, (crs.length : ℝ) ≤ c * (n lam : ℝ)

/-- The completeness experiment at `λ`, as a Boolean: `crs ← Gen(1^λ)`, `x ← A^O(crs)` (output `0`
of the chooser), `π ← P^O(crs, x)`; the bad event is
`x ∈ {0,1}^{n(λ)} ∧ C^O(x) = 1 ∧ V^O(crs, x, π) = 0`. -/
noncomputable def completenessFail (n : ℕ → ℕ) (N : ℕ → ℕ) (S : Scheme) (O : Oracle)
    (A : ℕ → RCircuit) (lam : ℕ) : PMF Bool := do
  let crs ← S.gen lam
  let xs ← (A lam).run O [crs]
  let x := xs.getD 0 []
  let ps ← (S.prover lam).run O [crs, x]
  let π := ps.getD 0 []
  return decide (x.length = n lam ∧ C O (N lam) x = true ∧
    (S.verifier lam crs x π).eval O = false)

/-- **Adaptive completeness** (Definition 17, p. 17, "the probability of rejecting an accepting
execution remains negligible when (x, w) is chosen by a polynomial-size oracle algorithm after
seeing crs"): for every oracle `O` and every polynomial-size randomized oracle algorithm `A`
mapping `crs` to `x`, there is a negligible `ν` with
`Pr[x ∈ {0,1}^n ∧ C^O(x) = 1 ∧ V^O(crs, x, π) = 0] ≤ ν(λ)` for every `λ`. -/
def AdaptiveComplete (n N : ℕ → ℕ) (S : Scheme) : Prop :=
  ∀ O : Oracle, ∀ A : ℕ → RCircuit, IsPolySize A →
    ∃ ν : ℕ → ℝ, OWFLocalDesc.Negligible ν ∧
      ∀ lam : ℕ, (completenessFail n N S O A lam true).toReal ≤ ν lam

/-- The soundness experiment at `λ`, as a Boolean: `crs ← Gen(1^λ)`, `(x, π*) ← Adv^O(crs)`
(outputs `0` and `1` of the adversary); the bad event is
`x ∈ {0,1}^{n(λ)} ∧ x ∉ L^O ∧ C^O is ε-robust on x ∧ V^O(crs, x, π*) = 1`. -/
noncomputable def soundnessBreak (n : ℕ → ℕ) (N : ℕ → ℕ) (ε : ℝ) (S : Scheme) (O : Oracle)
    (Adv : ℕ → RCircuit) (lam : ℕ) : PMF Bool := do
  let crs ← S.gen lam
  let out ← (Adv lam).run O [crs]
  let x := out.getD 0 []
  let π := out.getD 1 []
  return decide (x.length = n lam ∧ C O (N lam) x = false ∧ Robust ε O (N lam) x ∧
    (S.verifier lam crs x π).eval O = true)

/-- **Adaptive soundness** (Definition 17, p. 17, public deterministic verifier): for every oracle
`O` and every polynomial-size randomized oracle adversary `Adv`, there is a negligible `μ` with
`Pr[x ∈ {0,1}^n ∧ x ∉ L^O ∧ C^O ε-robust on x ∧ V^O(crs, x, π*) = 1] ≤ μ(λ)` for every `λ`. -/
def AdaptiveSound (n N : ℕ → ℕ) (ε : ℝ) (S : Scheme) : Prop :=
  ∀ O : Oracle, ∀ Adv : ℕ → RCircuit, IsPolySize Adv →
    ∃ μ : ℕ → ℝ, OWFLocalDesc.Negligible μ ∧
      ∀ lam : ℕ, (soundnessBreak n N ε S O Adv lam true).toReal ≤ μ lam

end OracleSNARG.PublicLB


