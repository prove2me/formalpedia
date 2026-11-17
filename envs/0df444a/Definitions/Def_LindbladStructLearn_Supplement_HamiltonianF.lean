-- Prove2me | Definitions.Def_LindbladStructLearn_Supplement_HamiltonianF
-- name    : LindbladStructLearn_Supplement_HamiltonianF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:40:39.157359+00:00
-- url     : https://prove2.me/theorems/2dda5b0b-5af2-409a-95f9-2ed0ce47a83e
-- title:
--   Expectation vectors $E$, error vectors $\mathcal F$, Jacobian $J$ and Algorithm 5 for Hamiltonians
-- statement:
--   For a $k$-local Hamiltonian with true coefficient vector $\lambda$ and an iterate $x\in\mathbb C^{\mathcal P_k}$, Section 5.6 defines expectation vectors for two access models (Eq. (5.126)):
--   $$E_P(x)=\mathop{\mathbb E}_{R\sim\mathcal P_{S_P}}\big[\overline{\operatorname{tr}}\big(e^{-iH(x)t}R\,e^{iH(x)t}RP\big)\big]\quad\text{(real time)},\qquad E_P(x)=\operatorname{tr}\big(P\rho_\beta(x)\big)\quad\text{(Gibbs state)}.$$
--   Here $\overline{\operatorname{tr}}=\operatorname{tr}/2^n$, $R$ is uniform over the $4^{|S_P|}$ Paulis supported in the support $S_P$ of $P$, and $\rho_\beta(x)=e^{-\beta H(x)}/\operatorname{tr}(e^{-\beta H(x)})$. The error vectors are
--   $$\mathcal F_P(x)=\tfrac1t\big(E_P(x)-E_P(\lambda)\big)\quad\text{(real time)},\qquad \mathcal F_P(x)=\tfrac{i}{\beta}\big(E_P(x)-E_P(\lambda)\big)\quad\text{(Gibbs state)}.$$
--   In both cases the first-order term of $\mathcal F_P(x)$ is $x_P-\lambda_P$. The Jacobian is $J_{P,Q}(x)=\partial_{x_Q}\mathcal F_P(x)$, the complex derivative. **Algorithm 5** sets $x^{(0)}=0$ and
--   $$x^{(j+1)}=\mathrm{Round}_{\varepsilon_j/4}\big(x^{(j)}-\widehat{\mathcal F}(x^{(j)})\big),\qquad \varepsilon_j=2^{-j},$$
--   where $\mathrm{Round}_\tau$ sets every entry of modulus at most $\tau$ to $0$. It returns $x^{(T)}$ with $T=\lceil\log_2(1/\varepsilon)\rceil$.
--
--   These are the objects of Theorem 5.11.
--
--   **Formalization Note** The page prints the Gibbs error vector as $-\frac1\beta E_P(x)+\frac1\beta E_P(\lambda)$. Footnote 10 says this sign was chosen so that its first-order term matches the real-time case, namely $x_P$. With $H(x)=i\sum_P x_PP$ one has $E_P(x)=-i\beta x_P+O(\beta^2)$, so the printed formula gives $i(x_P-\lambda_P)$ instead. The normalization $i/\beta$ is the one footnote 10 asks for. It is the real-coefficient normalization $-1/\beta$ of [HKT24] after substituting $h=ix$. The estimates may depend on the round. When $\operatorname{tr}(e^{-\beta H(x)})=0$, which can only happen for a non-imaginary $x$, the Gibbs vector takes Lean's default value, and every statement assumes the trace is nonzero.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §5.6, Eqs. (5.126)–(5.129), footnote 10 and Algorithm 5, p.46

import Mathlib
import Definitions.Def_LindbladStructLearn_Supplement_HamiltonianModel
import Definitions.Def_LindbladStructLearn_pauliAvg
import Definitions.Def_LindbladStructLearn_ntr
import Definitions.Def_LindbladStructLearn_roundVec

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix

namespace LindbladStructLearn.Supplement

open LindbladTolerant.Testing

/-- The real-time expectation vector (Lewis–Tang–Wright, *Learning the structure of open quantum
systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §5.6, Eq. (5.126), p.46):
`E_P(x) = E_(R∼𝒫_(S_P)) [tr̄(e^(−iH(x)t) R e^(iH(x)t) R P)]`, for every `k`-local non-identity `P`.

**Formalization Note** `tr̄ = tr/2ⁿ` is the published `ntr` (the overline is visible on the rendered
page); `E_(R∼𝒫_S)` is the published `pauliAvg` (uniform over the `4^|S|` Paulis supported in `S`).
Defined for every complex `x` (both exponentials are written as printed, not as an adjoint). -/
noncomputable def rtExpVec {n k : ℕ} (t : ℝ) (x : HIdx n k → ℂ) : HIdx n k → ℂ := fun P =>
  pauliAvg (support P.1) fun R =>
    ntr (NormedSpace.exp ((-((t : ℂ) * Complex.I)) • hamOp x) * pauliMatrix R *
      NormedSpace.exp (((t : ℂ) * Complex.I) • hamOp x) * pauliMatrix R * pauliMatrix P.1)

/-- The real-time error vector (§5.6, Eq. (5.127), p.46): `F_P(x) = E_P(x)/t − E_P(λ)/t`, with `λ`
the true coefficient vector. -/
noncomputable def rtF {n k : ℕ} (t : ℝ) (lam x : HIdx n k → ℂ) : HIdx n k → ℂ := fun P =>
  (rtExpVec t x P - rtExpVec t lam P) / (t : ℂ)

/-- The Gibbs-state expectation vector (§5.6, Eq. (5.126), p.46): `E_P(x) = tr(P ρ_β(x))` with
`ρ_β(x) = e^(−βH(x))/tr(e^(−βH(x)))` (plain trace; `ρ_β` is the published `WolfAreaLaw.thermalState`).

**Formalization Note** Where `tr(e^(−βH(x))) = 0` (possible only for non-imaginary `x`) the thermal
state is the zero matrix; every statement using this vector assumes the trace is nonzero. -/
noncomputable def gibbsExpVec {n k : ℕ} (β : ℝ) (x : HIdx n k → ℂ) : HIdx n k → ℂ := fun P =>
  (pauliMatrix P.1 * WolfAreaLaw.thermalState β (hamOp x)).trace

/-- The Gibbs-state error vector (§5.6, Eq. (5.127) and footnote 10, p.46), normalized so that its
first-order term is `x_P − λ_P`: `F_P(x) = (i/β)(E_P(x) − E_P(λ))`.

**Formalization Note** The page prints `F_P(x) = −E_P(x)/β + E_P(λ)/β` and states in footnote 10 that
the sign is chosen "to make the first order terms match", i.e. so that `F_P(x) = x_P − λ_P + O(β)` as
in the real-time case. With the paper's `H(x) = i Σ x_P P` one has `E_P(x) = −iβ x_P + O(β²)`, so the
printed normalization gives `i(x_P − λ_P)` and a Jacobian near `i·I`, against which hypothesis (5.131)
can hold only when `λ = 0` for small `β`. The factor `i/β` realizes footnote 10's stated intent (it is
the real-coefficient normalization `−1/β` of [HKT24] after the substitution `h = i x`). -/
noncomputable def gibbsF {n k : ℕ} (β : ℝ) (lam x : HIdx n k → ℂ) : HIdx n k → ℂ := fun P =>
  (Complex.I / (β : ℂ)) * (gibbsExpVec β x P - gibbsExpVec β lam P)

/-- The Jacobian of a vector function (§5.6, p.46): `J_(P,Q)(x) = ∂_(x_Q) F_P(x)`.

**Formalization Note** The complex (holomorphic) derivative: the Fréchet derivative over `ℂ` of
`F_P` at `x`, applied to the `Q`-th unit vector. Iterates are complex vectors, and both `F`'s are
holomorphic where defined. -/
noncomputable def jac {n k : ℕ} (F : (HIdx n k → ℂ) → HIdx n k → ℂ) (x : HIdx n k → ℂ)
    (P Q : HIdx n k) : ℂ :=
  fderiv ℂ (fun y => F y P) x (Pi.single Q 1)

/-- Algorithm 5 (structure learning algorithm for Hamiltonians, §5.6, Eq. (5.129), p.46):
`x^(0) = 0` and `x^(j+1) = Round_(ε_j/4)(x^(j) − F̂(x^(j)))` with `ε_j = 2^(−j)`; the output is
`x^(T)`, `T = ⌈log₂(1/ε)⌉`.

**Formalization Note** The estimates may depend on the round: `F̂ j` is used in round `j`. Rounding is
the published `roundVec` (`|·| ≤ τ` is set to `0`). -/
noncomputable def alg5Iter {n k : ℕ} (Fhat : ℕ → (HIdx n k → ℂ) → (HIdx n k → ℂ)) :
    ℕ → HIdx n k → ℂ
  | 0 => 0
  | j + 1 =>
    let x := alg5Iter Fhat j
    roundVec ((1 / 2 ^ j : ℝ) / 4) (x - Fhat j x)

end LindbladStructLearn.Supplement


