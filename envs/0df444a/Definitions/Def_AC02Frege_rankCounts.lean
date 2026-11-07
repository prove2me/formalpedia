-- Prove2me | Definitions.Def_AC02Frege_rankCounts
-- name    : AC02Frege_rankCounts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:26.886909+00:00
-- url     : https://prove2.me/theorems/165cfac1-6325-440d-a096-6df909e3bab8
-- title:
--   Monomial counts $M_N(j)$, spaces $V_j(x)$, the threshold $h$, excluded counts $E_j$, $\varepsilon$, error spaces $Z_P(j)$, ranks $c_P(j)$ and $\eta$
-- statement:
--   Let $N=n\ell$. The monomial count is $M_N(K)=\sum_{j=0}^{K}\binom Nj$, and $V_j(x)$ is the space of multilinear polynomials of degree at most $j$ in the lifted variables, of dimension $M_N(j)$. With $B=V_K(x)\cap\widehat C_D$, the **threshold** is
--   $$
--   h=M_N(K)-\dim B .
--   $$
--   For $0\le j\le K$, $E_j$ is the number of monomials $x_T$ with $|T|\le j$ and $|J(T)|>Q$, and
--   $$
--   \varepsilon=\max_{0\le j\le K}\frac{\#\{T:|T|=j,\ |J(T)|>Q\}}{\binom Nj}.
--   $$
--   For a line with polynomials $u_1,\dots,u_s$ and an intermediate approximator $P$, the error solution space and its rank are
--   $$
--   Z_P(j)=\{f\in V_j(x): fPu_i\in\widehat C_D \text{ for every } i\},\qquad c_P(j)=M_N(j)-\dim Z_P(j),
--   $$
--   and $\eta(d)=\tfrac12 M_N(K-d)/M_N(K)$.
--
--   **Formalization Note** Dimensions are `Module.finrank` of the $\mathbb F_2$-span; every set involved lies inside some $V_j(x)$, so this is its true dimension. $Z_P(j)$ is defined by membership in $\widehat C_D$, as the kernel of the error map of Definition 4.14, without choosing a basis. Products are products of functions.
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Definition 2.8, p.11; Definitions 4.13–4.14, p.24; (26), p.25; §5.3, p.31

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_majorityExpansion

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- The monomial count `M_N(K) = Σ_{j=0}^{K} C(N, j)` (Definition 2.8, p.11), the number of
multilinear monomials of degree at most `K` in `N` variables. -/
def monoCount (N K : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (K + 1), N.choose j

/-- `V_j`: the multilinear polynomials of degree at most `j` (Definition 2.8, p.11;
Definition 4.13, p.24). -/
def Vdeg (V : Type*) (j : ℕ) : Set (MvPolynomial V (ZMod 2)) :=
  {f | IsMultilinear f ∧ f.totalDegree ≤ j}

/-- The dimension of (the span of) a set of polynomials over `𝔽₂`.

**Formalization Note** Every set this is applied to is a subspace of some `V_j`, so the span is
the set itself and the `finrank` is its true (finite) dimension. -/
noncomputable def dimSpan {V : Type*} (S : Set (MvPolynomial V (ZMod 2))) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) S)

/-- The threshold `h = M_N(K) − dim B` with `B = V_K(x) ∩ Ĉ_D` (Definition 4.13, p.24), in the
`N = nℓ` lifted variables. -/
noncomputable def hThresh {n : ℕ} (F : CNF (Fin n)) (ℓ D K : ℕ) : ℕ :=
  monoCount (n * ℓ) K - dimSpan (Vdeg (Fin n × Fin ℓ) K ∩ CHat F ℓ D)

/-- `E_j = #{T : |T| ≤ j, |J(T)| > Q}` (Definition 4.13, p.24), the number of monomials of degree
at most `j` excluded by `W_Q`. -/
def Eexcl (n ℓ Q j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter
    (fun T => T.card ≤ j ∧ Q < (heavyBlocks T).card)).card

/-- The largest excluded fraction in a single degree (Definition 4.13, p.24):
`ε = max_{0 ≤ j ≤ K} #{T : |T| = j, |J(T)| > Q} / C(N, j)`. -/
noncomputable def epsExcl (n ℓ Q K : ℕ) : ℝ :=
  (Finset.range (K + 1)).sup' ⟨0, by simp⟩ (fun j =>
    ((((Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter
      (fun T => T.card = j ∧ Q < (heavyBlocks T).card)).card : ℕ) : ℝ) / ((n * ℓ).choose j : ℝ))

/-- The solution space `Z_P(j) = {f ∈ V_j(x) : f P u_i ∈ Ĉ_D for every i}` of the error
conditions of a line with polynomials `u_1, …, u_s` and intermediate approximator `P`
(Definition 4.14, p.24). Products are multilinearized (membership in `Ĉ_D` depends only on the
function). -/
def Zsol {n : ℕ} (F : CNF (Fin n)) (ℓ D j : ℕ) (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    {s : ℕ} (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    Set (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  {f | f ∈ Vdeg (Fin n × Fin ℓ) j ∧ ∀ i, f * P * u i ∈ CHat F ℓ D}

/-- The number of independent error conditions `c_P(j) = M_N(j) − dim Z_P(j)`
(Definition 4.14, p.24). -/
noncomputable def cErr {n : ℕ} (F : CNF (Fin n)) (ℓ D j : ℕ)
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) {s : ℕ}
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : ℕ :=
  monoCount (n * ℓ) j - dimSpan (Zsol F ℓ D j P u)

/-- The fraction `η(d) = ½ M_N(K − d) / M_N(K)` ((26), p.25; §5.3, p.31). -/
noncomputable def etaFrac (N K d : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (monoCount N (K - d) : ℝ) / (monoCount N K : ℝ)

end AC02Frege


