-- Prove2me | Definitions.Def_StrongConv
-- name    : StrongConv
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T22:35:43.371428+00:00
-- url     : https://prove2.me/theorems/51bc4a6f-e3e0-4354-a595-86f7d5680811
-- title:
--   Random permutation matrices, the free-group model, and compactly supported distributions (Chen–Garza-Vargas–Tropp–van Handel 2026)
-- statement:
--   The objects of Chen–Garza-Vargas–Tropp–van Handel's paper. Page numbers are those of arXiv:2405.16026v3. The free generators $g_1, \dots, g_d$ and the permutations $\sigma_1, \dots, \sigma_d$ are indexed by `Fin d`, so the paper's index $i \in \{1, \dots, d\}$ is $i - 1$ here.
--
--   **Probability.** p. 13: “Then we can define random matrices $\Pi^N_1, \dots, \Pi^N_d$ of dimension $\dim V_N$ as $\Pi^N_i := \pi_N(\sigma_i)$, (3.1) where $\sigma_1, \dots, \sigma_d$ are i.i.d. uniformly distributed elements of $\mathbf S_N$. When $\pi_N$ is the standard representation, we recover the random permutation matrices $\Pi^N_i = S^N_i$ as a special case.” So a probability or an expectation over $d$ random permutations of $\{1, \dots, N\}$ is a normalized count or average over `Fin d → Equiv.Perm (Fin N)`: `uniformProb E` is the proportion of tuples satisfying $E$, and `uniformExp f` is the average of $f$.
--
--   **Random permutation matrices (p. 9).** “**Definition 3.1.** Let $\bar S^N_1, \dots \bar S^N_d$ be i.i.d. random permutation matrices of dimension $N$, and denote by $S^N_i := \bar S^N_i|_{\{1_N\}^\perp}$ their restriction to the invariant subspace $\{1_N\}^\perp \subset \mathbb C^N$. We will often write $\boldsymbol S^N = (S^N_1, \dots, S^N_d)$ and $\boldsymbol S^{N*} = (S^{N*}_1, \dots, S^{N*}_d)$.”
--   - p. 3: “$1_N \in \mathbb C^N$ denotes the vector all of whose entries equal one.” `onesVec N` is $1_N$ and `OnesPerp N` is $\{1_N\}^\perp \subseteq \mathbb C^N$ (Euclidean).
--   - `permOp σ` is the permutation matrix $\bar S_\sigma$ with $\bar S_\sigma e_j = e_{\sigma(j)}$. `permOpPerp σ` is its restriction to $\{1_N\}^\perp$, and `sModel σ` is the tuple $\boldsymbol S^N = (S_{\sigma_1}, \dots, S_{\sigma_d})$.
--   - p. 9: “Then $A^N := \bar A^N|_{\{1_N\}^\perp}$ is defined by the linear polynomial of random permutation matrices $A^N := S^N_1 + S^{N*}_1 + \cdots + S^N_d + S^{N*}_d$”. This is `adjPerp σ`.
--
--   **The limiting model (p. 9).** “**Definition 3.2.** Let $\boldsymbol s = (s_1, \dots, s_d)$ be defined by $s_i := \lambda(g_i)$, where $g_1, \dots, g_d$ are the free generators of $\mathbf F_d$ and $\lambda : \mathbf F_d \to B(l^2(\mathbf F_d))$ is the left-regular representation defined by $\lambda(g)\delta_h = \delta_{gh}$. Define the vector state $\tau(a) := \langle \delta_e, a\delta_e\rangle$ on $B(l^2(\mathbf F_d))$.”
--   - `L2Free d` is $l^2(\mathbf F_d)$, `delta v` is $\delta_v$, `leftReg g` is $\lambda(g)$ (acting by $(\lambda(g)f)(h) = f(g^{-1}h)$), `sLimit d` is $\boldsymbol s$, and `tau` is $\tau$.
--   - p. 9: “and the associated limiting model is $A_{\rm F} := s_1 + s_1^* + \cdots + s_d + s_d^*$.” This is `adjFree d`.
--   - `trTau Y` is $(\mathrm{tr}_D \otimes \tau)(Y) = \frac1D\sum_{a} \langle e_a \otimes \delta_e, Y(e_a \otimes \delta_e)\rangle$, the functional of Corollary 7.2.
--
--   **Traces (pp. 3, 9).** p. 3: “The trace of a matrix $M$ is denoted as $\mathrm{Tr}\,M$, the normalized trace as $\mathrm{tr}_N M := \frac1N \mathrm{Tr}\,M$”. p. 9: “*Remark* 3.3. Even though $S^N_i$ are $(N-1)$-dimensional matrices defined on $\{1_N\}^\perp$, we will normalize the trace $\mathrm{tr}_N$ by $N$ rather than by $N - 1$”. So `trN N Y` is $\frac1N$ times the trace of an operator $Y$ on $\{1_N\}^\perp$, and `trDN D N Y` is $\frac1{DN}$ times the trace of an operator on $D$ copies of $\{1_N\}^\perp$. Both take the real part of the trace, which is real in every use here.
--
--   **Functional calculus (p. 3).** “If $X$ is a self-adjoint operator and $h : \mathbb R \to \mathbb C$, then the operator $h(X)$ is defined by the usual functional calculus”. For a real function $h$, `fnCalc h X` is the continuous functional calculus of the C*-algebra applied to $z \mapsto h(\operatorname{Re} z)$. For self-adjoint $X$ and continuous $h$ this is $h(X)$, since the spectrum is real.
--
--   **Noncommutative polynomials (p. 12).** “We will formulate our strong convergence results for general noncommutative polynomials $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ with matrix coefficients, that is, $P(\boldsymbol s, \boldsymbol s^*) = \sum_w A_w \otimes w(\boldsymbol s, \boldsymbol s^*)$, where the sum is over a finite set of words $w$ in the symbols $s_1, \dots, s_d, s_1^*, \dots, s_d^*$ and $A_w \in \mathrm M_D(\mathbb C)$ are matrix coefficients.”
--   - `NCPoly D d` is a finitely supported map from words in the letters `Sum.inl i` ($s_i$) and `Sum.inr i` ($s_i^*$) to $D \times D$ complex matrices.
--   - `NCPoly.eval` is $P(\boldsymbol u, \boldsymbol u^*)$ for a $d$-tuple $\boldsymbol u$ of operators on a Hilbert space $H$. It acts on $D$ copies of $H$ (the $\ell^2$-sum, standing for $\mathbb C^D \otimes H$). A word acts as the product of its letters in the order they appear, and $A \otimes T$ (`tensorOp`) has $(a, b)$ block $A_{ab}T$.
--   - `NCPoly.IsSelfAdjoint` is $P^* = P$ for the formal adjoint $\big(\sum_w A_w \otimes w\big)^* = \sum_w A_w^* \otimes w^*$, where $w^*$ reverses $w$ and exchanges $s_i$ with $s_i^*$. `NCPoly.degree` is the largest length of a word with a nonzero coefficient; "of degree $q_0$" is read as "`NCPoly.degree` of $P$ at most $q_0$" throughout.
--   - p. 12: “For any such polynomial, we define the norm $\|P\|_{\mathrm M_D(\mathbb C) \otimes C^*(\mathbf F_d)} = \sup_{\boldsymbol U} \|P(\boldsymbol U, \boldsymbol U^*)\|$, where the supremum is taken over all $d$-tuples of unitary matrices of any dimension.” This is `NCPoly.fullNorm`. Its agreement with the norm of the full $C^*$-algebra of the free group, which the paper cites to Choi [17, Theorem 7], is the milestone `StrongConv.norm_toFull_eq_fullNorm`, about $C^*(\mathbf F_d)$ itself (`FullGroupCStar`).
--   - `expTr P N h` is $\mathbf E[\mathrm{tr}_{DN}\, h(P(\boldsymbol S^N, \boldsymbol S^{N*}))]$.
--
--   **The functionals $\nu_i$ (pp. 20–21).** Theorem 6.1 asserts the existence of linear functionals $\nu_i$ on polynomials with $\big|\mathbf E[\mathrm{tr}_{DN}\, h(P(\boldsymbol S^N, \boldsymbol S^{N*}))] - \sum_{i<m} \nu_i(h)/N^i\big| = O(N^{-m})$; such functionals are the coefficients of the asymptotic expansion in $1/N$. `asympCoeff F m` is that coefficient, defined recursively by $c_m = \lim_{N\to\infty} N^m\big(F(N) - \sum_{i<m} c_i/N^i\big)$. `nu P i h` is the $i$-th coefficient for $F(N) = $ `expTr P N h`, and `nuAdj d i h` is the same for $\mathbf E[\mathrm{tr}_N\, h(A^N)]$. The proof on p. 21 defines $\nu_m(h) := \Psi_h^{(m)}(0)/m!$ for the rational function $\Psi_h$ of $1/N$; the two agree wherever the expansion holds, which is what Theorem 6.1 asserts.
--
--   **Norms of functions (p. 3).** “We denote by $h^{(m)}$ the $m$th derivative of a univariate function, and by $\|h\|_{C^m[a,b]} := \sum_{j=0}^m \sup_{x \in [a,b]} |h^{(j)}(x)|$.” This is `cNorm m h a b`, with `supOn f a b` $= \sup_{x \in [a, b]} |f(x)|$. `lpNormCircle β f` is $\|f\|_{L^\beta[0, 2\pi]}$ for Lebesgue measure, and `conjExp β` is $\beta_*$ with $1/\beta_* = 1 - 1/\beta$ (p. 16).
--
--   **Compactly supported distributions (p. 17).** “**Definition 4.6.** A linear functional $\nu$ on $C^\infty(\mathbb R)$ such that $|\nu(f)| \le c\|f\|_{C^m[-K,K]}$ for all $f \in C^\infty(\mathbb R)$ holds for some $c, K > 0$, $m \in \mathbb Z_+$, is called a *compactly supported distribution*.”
--   - `smoothFun` is $C^\infty(\mathbb R)$, real-valued smooth functions; `polyFun h` is a real polynomial as an element of it. `IsCSDistribution ν` is Definition 4.6 for an $\mathbb R$-linear $\nu$. The test functions are real-valued, as are all of the paper's test functions ($h \in \mathcal P$, $\chi$).
--   - p. 17: “**Definition 4.8.** The *support* $\operatorname{supp} \nu$ of a compactly supported distribution $\nu$ is the smallest closed set $A \subset \mathbb R$ with the property that $\nu(f) = 0$ for every $f \in C^\infty(\mathbb R)$ such that $f = 0$ in a neighborhood of $A$.” `supp ν` is the intersection of all closed sets with that property (`VanishesNear`). That this intersection itself has the property, so that it is the smallest such set, is the standard fact that the definition presupposes.
--
--   **Words (pp. 19–20).** p. 19: “It will be convenient to extend these definitions by setting $g_0 := e$, $g_{d+i} := g_i^{-1}$ and analogously $S^N_0 := \mathbf 1$, $S^N_{d+i} := (S^N_i)^{-1} = S^{N*}_i$ and $s_0 := \mathbf 1$, $s_{d+i} := s_i^{-1} = s_i^*$ for $1 \le i \le d$.” And: “denote by $\mathbf W_d$ the set of all finite words in the letters $g_0, \dots, g_{2d}$.”
--   - `Letter d` is a letter: `none` for $g_0$, `some (Sum.inl i)` for $g_i$, `some (Sum.inr i)` for $g_{d+i}$. A word is a list of letters.
--   - p. 19: “We implicitly identify $w \in \mathbf W_d$ with the word map $w : \mathrm G^d \to \mathrm G$ it induces on any group $\mathrm G$. Thus $w(g_1, \dots, g_d) \in \mathbf F_d$ is the reduction of the word $w$, while $w(S^N_1, \dots, S^N_d)$ is the random matrix obtained by substituting $g_i \leftarrow S^N_i$ and multiplying these matrices in the order they appear in $w$.” `wordFree w` is the reduction $w(g_1, \dots, g_d)$. `wordEval u w` is $w(\boldsymbol u)$ for a tuple of operators: $g_0 \mapsto 1$, $g_i \mapsto u_i$, and $g_{d+i} \mapsto u_i^*$, which is $u_i^{-1}$ for the unitary tuples $\boldsymbol S^N$ and $\boldsymbol s$ (p. 19: “$S^N_{d+i} := (S^N_i)^{-1} = S^{N*}_i$”).
--   - p. 20: “An element of the free group $v \in \mathbf F_d$, $v \ne e$ is called a *proper power* if it can be written as $v = w^k$ for some $w \in \mathbf F_d$ and $k \ge 2$, and is called a *non-power* otherwise.” This is `IsNonPower v` ($v \ne e$ and not a proper power).
--   - `gPoly d q` is $g_q(x) := (1 - x)^{d_1}(1 - 2x)^{d_2} \cdots (1 - (q-1)x)^{d_{q-1}}$ with $d_j := \min(d, \lfloor \frac{q}{j+1}\rfloor)$ (Lemma 5.1, p. 19).
--
--   **The staircase (p. 10).** `rhoStair d m` is $\rho_m$ of Theorem 3.6: $2\sqrt{2d-1}$ for $2m - 1 \le \sqrt{2d-1}$, and $2m - 1 + \frac{2d-1}{2m-1}$ for $2m - 1 > \sqrt{2d-1}$. `mStar d` is $m_* := \lfloor \frac12(\sqrt{2d-1} + 1)\rfloor$.
--
--   **Stable representations (pp. 13–14).** p. 13: “Following [32], denote by $\xi_i(\sigma)$ the number of fixed points of $\sigma^i$ for $\sigma \in \mathbf S_N$.” And: “**Definition 3.13.** A finite-dimensional unitary representation $\pi_N : \mathbf S_N \to B(V_N)$ of $\mathbf S_N$, defined for each $N \ge N_0$, is *stable* if there exists $r \in \mathbb N$ and a polynomial $\varphi \in \mathbb C[x_1, \dots, x_r]$ so that $\mathrm{Tr}\, \pi_N(\sigma) = \varphi(\xi_1(\sigma), \dots, \xi_r(\sigma))$ for all $N \ge N_0$, $\sigma \in \mathbf S_N$.”
--   - `xi i σ` is $\xi_i(\sigma)$.
--   - A `StableRep` carries $N_0$, $r$, the character polynomial $\varphi$ and, for each $N$, a unitary representation $\pi_N$ of $\mathbf S_N$ on $\mathbb C^{D_N}$ (`dim N` $= D_N$), with $\mathrm{Tr}\,\pi_N(\sigma) = \varphi(\xi_1(\sigma), \dots, \xi_r(\sigma))$ for $N \ge N_0$. The representations for $N < N_0$ play no role. This follows §3.4.2, p. 14: “Fix a stable representation $\pi_N : \mathbf S_N \to B(V_N)$ defined for $N \ge N_0$ by a character polynomial $\varphi \in \mathbb C[x_1, \dots, x_r]$.”
--   - p. 14: “We will not require that $\pi_N$ is irreducible, but we assume it does not contain the trivial representation.” `NoTrivialSummand` says that for $N \ge N_0$ no nonzero vector is fixed by every $\pi_N(\sigma)$.
--   - p. 14: “$D_N := \dim(V_N) = \mathrm{Tr}\,\pi_N(e) = \varphi(N, N, \dots, N)$. Thus $D_N$ is a polynomial in $N$; we denote its degree by $\alpha$”. `alpha` is the degree of the one-variable polynomial $\varphi(X, \dots, X)$.
--   - `model σ` is $\boldsymbol\Pi^N = (\pi_N(\sigma_1), \dots, \pi_N(\sigma_d))$ (p. 13, (3.1)).
--
--   **Linearization (p. 27).** Lemma 9.1 uses operators $X_j := \sum_{i=0}^{2d} A_{j,i} \otimes \lambda(g_i)$ “with matrix coefficients $A_{j,i}$ of dimensions $D_j \times D_{j+1}$”. `linOp A` is $\sum_{i=0}^{2d} A_i \otimes \lambda(g_i)$ (with $g_0 = e$, $g_{d+i} = g_i^{-1}$). `linChain Dim A t k` is the product $X_t X_{t+1} \cdots X_{t+k-1}$. `linChainOn Dim A q h₁ hq` is $X_1 \cdots X_q$ as an operator on $D$ copies of $l^2(\mathbf F_d)$ when $D_1 = D_{q+1} = D$: the end spaces are identified by `finCongr`, which is the identity on indices.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), pp. 3–29, Notation (p. 3), Definitions 3.1–3.2 and Remark 3.3 (p. 9), noncommutative polynomials and their full norm (p. 12), stable representations (Definition 3.13 and §3.4.2, pp. 13–14), compactly supported distributions and their support (Definitions 4.6 and 4.8, pp. 17–18), words (§5, pp. 19–20), the staircase ρ_m (Theorem 3.6, p. 10), the functionals ν_i (Theorem 6.1, pp. 20–21) and the linearization operators (Lemma 9.1, p. 27)

import Mathlib

/-!
# Random permutation matrices, their limiting model, and compactly supported distributions

C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*,
Ann. of Math. 203 (2026) 555–602, arXiv:2405.16026v3 (CGTvH; page numbers are those of the arXiv
version).

Conventions:
- The free generators `g₁, …, g_d` of `F_d` and the permutations `σ₁, …, σ_d` are indexed by `Fin d`,
  so the paper's index `i ∈ {1, …, d}` is `i - 1 : Fin d` here.
- A noncommutative polynomial with `D × D` matrix coefficients is a finitely supported function from
  words in the letters `Sum.inl i` (standing for `sᵢ`) and `Sum.inr i` (standing for `sᵢ*`) to
  `D × D` complex matrices. A word acts as the product of its letters in the order they appear.
- An operator with matrix coefficients acts on `D` copies of a Hilbert space `H`, the `ℓ²`-sum
  `PiLp 2 (fun _ : Fin D => H)`, which plays the role of `ℂᴰ ⊗ H`.
- Probabilities and expectations over i.i.d. uniform permutations are normalized counts over
  `Fin d → Equiv.Perm (Fin N)`.
- A real test function `h` is applied to an operator `T` by `fnCalc h T`, the complex continuous
  functional calculus applied to `z ↦ h(Re z)`.
-/

noncomputable section

namespace StrongConv

open Matrix Polynomial Filter
open scoped InnerProductSpace

/-! ## Uniform probability on a finite set -/

/-- The probability of an event under the uniform distribution on a finite type. -/
def uniformProb {X : Type*} [Fintype X] (E : X → Prop) : ℝ := by
  classical exact ((Finset.univ.filter E).card : ℝ) / (Fintype.card X : ℝ)

/-- The expectation of a real function under the uniform distribution on a finite type. -/
def uniformExp {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card X : ℝ)

/-! ## Functional calculus -/

/-- `h(T)`: the continuous functional calculus of the C*-algebra `A` applied to `z ↦ h(Re z)`. -/
def fnCalc {A : Type*} [CStarAlgebra A] (h : ℝ → ℝ) (T : A) : A :=
  cfc (fun z : ℂ => ((h z.re : ℝ) : ℂ)) T

/-! ## Operators with matrix coefficients -/

section Tensor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `A ⊗ T`: the operator from `n` copies of `H` to `m` copies of `H` whose `(a, b)` block is
`A a b • T`. -/
def tensorOp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin m => H) :=
  ∑ a : Fin m, ∑ b : Fin n, A a b •
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => H)).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.single ℂ (fun _ : Fin m => H) a).comp
        (T.comp (PiLp.proj 2 (fun _ : Fin n => H) b))))

/-- A letter `sᵢ` (`Sum.inl i`) or `sᵢ*` (`Sum.inr i`) evaluated at a `d`-tuple of operators. -/
def letterOp {d : ℕ} (u : Fin d → H →L[ℂ] H) : Fin d ⊕ Fin d → H →L[ℂ] H
  | Sum.inl i => u i
  | Sum.inr i => star (u i)

/-- A word in `s₁, …, s_d, s₁*, …, s_d*` evaluated at a `d`-tuple of operators: the product of its
letters in the order they appear. -/
def wordOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    H →L[ℂ] H :=
  (w.toList.map (letterOp u)).prod

end Tensor

/-- CGTvH p. 12: a noncommutative polynomial `P ∈ M_D(ℂ) ⊗ ℂ⟨s, s*⟩` in `d` variables with `D × D`
matrix coefficients, `P = ∑_w A_w ⊗ w`. -/
abbrev NCPoly (D d : ℕ) := FreeMonoid (Fin d ⊕ Fin d) →₀ Matrix (Fin D) (Fin D) ℂ

namespace NCPoly

variable {D d : ℕ}

/-- The formal adjoint of a word: reverse it and exchange `sᵢ` with `sᵢ*`. -/
def wordStar (w : FreeMonoid (Fin d ⊕ Fin d)) : FreeMonoid (Fin d ⊕ Fin d) :=
  FreeMonoid.ofList (w.toList.reverse.map Sum.swap)

/-- `P` is self-adjoint: `P* = P`, where `(∑ A_w ⊗ w)* = ∑ A_w* ⊗ w*`. -/
def IsSelfAdjoint (P : NCPoly D d) : Prop :=
  ∀ w, P (wordStar w) = (P w)ᴴ

/-- The degree of `P`: the largest length of a word with a nonzero coefficient. -/
def degree (P : NCPoly D d) : ℕ :=
  P.support.sup FreeMonoid.length

/-- `P(u, u*)`: the polynomial evaluated at a `d`-tuple of operators on `H`, an operator on `D`
copies of `H`. -/
def eval {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H) :=
  ∑ w ∈ P.support, tensorOp (P w) (wordOp u w)

/-- CGTvH p. 12: `‖P‖_{M_D(ℂ) ⊗ C*(F_d)} = sup_U ‖P(U, U*)‖`, the supremum over all `d`-tuples of
unitary matrices of any dimension. -/
def fullNorm (P : NCPoly D d) : ℝ :=
  sSup {x | ∃ (n : ℕ) (U : Fin d → Matrix.unitaryGroup (Fin n) ℂ),
    x = ‖P.eval (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (U i : Matrix (Fin n) (Fin n) ℂ))‖}

end NCPoly

/-! ## The free group and its left-regular representation (CGTvH Definition 3.2) -/

/-- `ℓ²(F_d)`. -/
abbrev L2Free (d : ℕ) := lp (fun _ : FreeGroup (Fin d) => ℂ) 2

/-- The coordinate vector `δ_v ∈ ℓ²(F_d)`. -/
def delta {d : ℕ} (v : FreeGroup (Fin d)) : L2Free d :=
  lp.single 2 v (1 : ℂ)

/-- The left-regular representation `λ(g)` on `ℓ²(F_d)`: `(λ(g) f)(h) = f(g⁻¹h)`, so that
`λ(g) δ_h = δ_{gh}`. -/
def leftReg {d : ℕ} (g : FreeGroup (Fin d)) : L2Free d →L[ℂ] L2Free d :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun h => f (g⁻¹ * h), by
        have hf := (lp.memℓp f)
        rw [memℓp_gen_iff (by norm_num)] at hf
        show Memℓp (fun h : FreeGroup (Fin d) => f (g⁻¹ * h)) 2
        rw [memℓp_gen_iff (by norm_num)]
        exact (Equiv.mulLeft g⁻¹).summable_iff.mpr hf⟩
      map_add' := fun f f' => by ext h; rfl
      map_smul' := fun c f => by ext h; rfl }
    1
    (by
      intro f
      rw [one_mul]
      apply le_of_eq
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
      congr 1
      exact (Equiv.mulLeft g⁻¹).tsum_eq (fun h => ‖f h‖ ^ (2 : ENNReal).toReal))

/-- CGTvH Definition 3.2: `s = (s₁, …, s_d)`, `sᵢ = λ(gᵢ)`. -/
def sLimit (d : ℕ) : Fin d → L2Free d →L[ℂ] L2Free d :=
  fun i => leftReg (FreeGroup.of i)

/-- CGTvH Definition 3.2: the vector state `τ(a) = ⟨δ_e, a δ_e⟩`. -/
def tau {d : ℕ} (a : L2Free d →L[ℂ] L2Free d) : ℂ :=
  ⟪delta 1, a (delta 1)⟫_ℂ

/-- `tr_D ⊗ τ` on operators on `D` copies of `ℓ²(F_d)`: `(1/D) ∑_a ⟨e_a ⊗ δ_e, Y (e_a ⊗ δ_e)⟩`. -/
def trTau {D d : ℕ}
    (Y : PiLp 2 (fun _ : Fin D => L2Free d) →L[ℂ] PiLp 2 (fun _ : Fin D => L2Free d)) : ℂ :=
  (D : ℂ)⁻¹ * ∑ a : Fin D,
    ⟪PiLp.single 2 a (delta 1), Y (PiLp.single 2 a (delta 1))⟫_ℂ

/-- CGTvH p. 9: `A_F = s₁ + s₁* + ⋯ + s_d + s_d*`, the adjacency operator of the `2d`-regular
tree. -/
def adjFree (d : ℕ) : L2Free d →L[ℂ] L2Free d :=
  ∑ i, (sLimit d i + star (sLimit d i))

/-! ## Random permutation matrices (CGTvH Definition 3.1) -/

/-- The all-ones vector `1_N ∈ ℂᴺ`. -/
def onesVec (N : ℕ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun _ => (1 : ℂ))

/-- The invariant subspace `{1_N}⊥ ⊆ ℂᴺ`. -/
abbrev OnesPerp (N : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin N)) :=
  (ℂ ∙ onesVec N)ᗮ

/-- The permutation matrix `S̄_σ` of `σ`, acting by `S̄_σ e_j = e_{σ j}`. -/
def permOp {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ).toContinuousLinearEquiv.toContinuousLinearMap

/-- CGTvH Definition 3.1: `S_σ = S̄_σ|_{1_N⊥}`, the permutation matrix restricted to `{1_N}⊥`. -/
def permOpPerp {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    OnesPerp N →L[ℂ] OnesPerp N :=
  ((permOp σ).comp (OnesPerp N).subtypeL).codRestrict (OnesPerp N) (fun ⟨x, hx⟩ => by
  have hones : (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ) (onesVec N) = onesVec N := by
    ext j
    simp [onesVec, LinearIsometryEquiv.piLpCongrLeft_apply]
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
  change ⟪onesVec N, (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ) x⟫_ℂ = 0
  rw [← hones, LinearIsometryEquiv.inner_map_map]
  exact hx)

/-- CGTvH Definition 3.1: `Sᴺ = (S₁ᴺ, …, S_dᴺ)` for a `d`-tuple of permutations. -/
def sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    Fin d → OnesPerp N →L[ℂ] OnesPerp N :=
  fun i => permOpPerp (σ i)

/-- CGTvH p. 9: `Aᴺ = S₁ᴺ + S₁ᴺ* + ⋯ + S_dᴺ + S_dᴺ*`, the adjacency matrix of the random
`2d`-regular graph restricted to `{1_N}⊥`. -/
def adjPerp {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    OnesPerp N →L[ℂ] OnesPerp N :=
  ∑ i, (sModel σ i + star (sModel σ i))

/-- CGTvH p. 3 and Remark 3.3: the trace on `D` copies of `{1_N}⊥` normalized by `DN` (not by
`D(N - 1)`), real part. -/
def trDN (D N : ℕ)
    (Y : PiLp 2 (fun _ : Fin D => OnesPerp N) →L[ℂ] PiLp 2 (fun _ : Fin D => OnesPerp N)) : ℝ :=
  (LinearMap.trace ℂ _ (Y : PiLp 2 (fun _ : Fin D => OnesPerp N) →ₗ[ℂ]
    PiLp 2 (fun _ : Fin D => OnesPerp N))).re / ((D : ℝ) * N)

/-- `tr_N` on `{1_N}⊥`, normalized by `N` (Remark 3.3), real part. -/
def trN (N : ℕ) (Y : OnesPerp N →L[ℂ] OnesPerp N) : ℝ :=
  (LinearMap.trace ℂ _ (Y : OnesPerp N →ₗ[ℂ] OnesPerp N)).re / N

/-- `E[tr_{DN} h(P(Sᴺ, Sᴺ*))]`. -/
def expTr {D d : ℕ} (P : NCPoly D d) (N : ℕ) (h : ℝ → ℝ) : ℝ :=
  uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trDN D N (fnCalc h (P.eval (sModel σ))))

/-! ## Asymptotic expansion coefficients -/

/-- The coefficients `c₀, c₁, …` of the asymptotic expansion `F(N) = ∑_{i < m} cᵢ / Nⁱ + o(N^{1-m})`:
`c_m = lim_{N → ∞} N^m (F(N) - ∑_{i < m} cᵢ / Nⁱ)`. -/
def asympCoeff (F : ℕ → ℝ) : ℕ → ℝ
  | m => limUnder Filter.atTop (fun N : ℕ =>
      (N : ℝ) ^ m * (F N - ∑ i : Fin m, asympCoeff F i / (N : ℝ) ^ (i : ℕ)))
decreasing_by exact i.isLt

/-- `νᵢ(h)`: the `i`-th coefficient of the expansion of `E[tr_{DN} h(P(Sᴺ, Sᴺ*))]` in powers of `1/N`
(CGTvH Theorem 6.1, pp. 20–21). -/
def nu {D d : ℕ} (P : NCPoly D d) (i : ℕ) (h : ℝ[X]) : ℝ :=
  asympCoeff (fun N => expTr P N (fun x => h.eval x)) i

/-- The same coefficients for `E[tr_N h(Aᴺ)]`. -/
def nuAdj (d : ℕ) (i : ℕ) (h : ℝ[X]) : ℝ :=
  asympCoeff (fun N => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
    trN N (fnCalc (fun x => h.eval x) (adjPerp σ)))) i

/-! ## Norms of real functions -/

/-- `sup_{x ∈ [a, b]} |f x|`. -/
def supOn (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sSup ((fun x => |f x|) '' Set.Icc a b)

/-- CGTvH p. 3: `‖f‖_{C^m[a,b]} = ∑_{j = 0}^m sup_{x ∈ [a,b]} |f^{(j)}(x)|`. -/
def cNorm (m : ℕ) (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), supOn (iteratedDeriv j f) a b

/-- `‖f‖_{L^β[0, 2π]}`. -/
def lpNormCircle (β : ℝ) (f : ℝ → ℝ) : ℝ :=
  (MeasureTheory.eLpNorm f (ENNReal.ofReal β)
    (MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)))).toReal

/-- The conjugate exponent `β*`, `1/β* = 1 - 1/β`. -/
def conjExp (β : ℝ) : ℝ := (1 - 1 / β)⁻¹

/-! ## Compactly supported distributions (CGTvH Definitions 4.6, 4.8) -/

/-- The space `C^∞(ℝ)` of smooth real functions. -/
def smoothFun : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f}
  add_mem' := fun {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) => hf.add hg
  zero_mem' := (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => (0 : ℝ))
  smul_mem' := fun _ {f} (hf : ContDiff ℝ (⊤ : ℕ∞) f) => contDiff_const.smul hf

/-- A real polynomial as an element of `C^∞(ℝ)`. -/
def polyFun (h : ℝ[X]) : smoothFun :=
  ⟨fun x => h.eval x, by
    have := (Polynomial.contDiff_aeval (𝕜 := ℝ) h ((⊤ : ℕ∞) : WithTop ℕ∞))
    simp only [Polynomial.coe_aeval_eq_eval] at this
    exact this⟩

/-- CGTvH Definition 4.6: a linear functional `ν` on `C^∞(ℝ)` is a compactly supported distribution
if `|ν(f)| ≤ c ‖f‖_{C^m[-K,K]}` for all `f`, for some `c, K > 0` and `m ∈ ℤ₊`. -/
def IsCSDistribution (ν : smoothFun →ₗ[ℝ] ℝ) : Prop :=
  ∃ (c K : ℝ) (m : ℕ), 0 < c ∧ 0 < K ∧ ∀ f : smoothFun, |ν f| ≤ c * cNorm m f (-K) K

/-- `ν(f) = 0` for every `f ∈ C^∞(ℝ)` that vanishes in a neighborhood of `A`. -/
def VanishesNear (ν : smoothFun →ₗ[ℝ] ℝ) (A : Set ℝ) : Prop :=
  ∀ f : smoothFun, (∀ᶠ x in nhdsSet A, (f : ℝ → ℝ) x = 0) → ν f = 0

/-- CGTvH Definition 4.8: the support of `ν`, the smallest closed set `A` with `ν(f) = 0` whenever
`f` vanishes in a neighborhood of `A`, written as the intersection of all such closed sets. -/
def supp (ν : smoothFun →ₗ[ℝ] ℝ) : Set ℝ :=
  ⋂₀ {A | IsClosed A ∧ VanishesNear ν A}

/-! ## Words in random permutation matrices (CGTvH §5) -/

/-- The letters `g₀ = e` (`none`), `g_i` (`some (Sum.inl i)`) and `g_{d+i} = g_i⁻¹`
(`some (Sum.inr i)`) of CGTvH §5. A word `w ∈ W_d` is a list of letters. -/
abbrev Letter (d : ℕ) := Option (Fin d ⊕ Fin d)

/-- The reduction `w(g₁, …, g_d) ∈ F_d` of a word. -/
def wordFree {d : ℕ} (w : List (Letter d)) : FreeGroup (Fin d) :=
  (w.map fun
    | none => 1
    | some (Sum.inl i) => FreeGroup.of i
    | some (Sum.inr i) => (FreeGroup.of i)⁻¹).prod

/-- A word evaluated at a `d`-tuple of operators: `g₀ ↦ 1`, `gᵢ ↦ uᵢ`, `g_{d+i} ↦ uᵢ*`, multiplied
in the order the letters appear. -/
def wordEval {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (u : Fin d → H →L[ℂ] H) (w : List (Letter d)) : H →L[ℂ] H :=
  (w.map fun
    | none => 1
    | some l => letterOp u l).prod

/-- CGTvH p. 20: `v ∈ F_d` is a non-power: `v ≠ e` and `v ≠ wᵏ` for every `w ∈ F_d` and `k ≥ 2`. -/
def IsNonPower {d : ℕ} (v : FreeGroup (Fin d)) : Prop :=
  v ≠ 1 ∧ ∀ (w : FreeGroup (Fin d)) (k : ℕ), 2 ≤ k → v ≠ w ^ k

/-- CGTvH Lemma 5.1: `g_q(x) = (1 - x)^{d₁} (1 - 2x)^{d₂} ⋯ (1 - (q - 1)x)^{d_{q-1}}` with
`d_j = min(d, ⌊q/(j + 1)⌋)`. -/
def gPoly (d q : ℕ) : ℝ[X] :=
  ∏ j ∈ Finset.Ico 1 q, (1 - (j : ℝ[X]) * X) ^ min d (q / (j + 1))

/-! ## The staircase (CGTvH Theorem 3.6) -/

/-- `ρ_m = 2√(2d-1)` if `2m - 1 ≤ √(2d-1)`, and `2m - 1 + (2d-1)/(2m-1)` otherwise. -/
def rhoStair (d m : ℕ) : ℝ :=
  if (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * d - 1) then 2 * Real.sqrt (2 * d - 1)
  else (2 * m - 1 : ℝ) + (2 * d - 1) / (2 * m - 1)

/-- `m* = ⌊(√(2d-1) + 1)/2⌋`, the largest `m` with `2m - 1 ≤ √(2d-1)`. -/
def mStar (d : ℕ) : ℕ :=
  ⌊(Real.sqrt (2 * d - 1) + 1) / 2⌋₊

/-! ## Stable representations of the symmetric group (CGTvH §3.4) -/

/-- `ξᵢ(σ)`: the number of fixed points of `σⁱ`. -/
def xi {N : ℕ} (i : ℕ) (σ : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => (σ ^ i) x = x).card

/-- CGTvH Definition 3.13 and §3.4.2: a stable representation, defined for `N ≥ N₀` by the character
polynomial `ϕ ∈ ℂ[x₁, …, x_r]`. For each `N`, `π N` is a unitary representation of `S_N` on
`ℂ^{dim N}`, and `Tr π_N(σ) = ϕ(ξ₁(σ), …, ξ_r(σ))` for all `N ≥ N₀` and `σ ∈ S_N`. -/
structure StableRep where
  N₀ : ℕ
  r : ℕ
  φ : MvPolynomial (Fin r) ℂ
  dim : ℕ → ℕ
  π : ∀ N, Equiv.Perm (Fin N) →* Matrix.unitaryGroup (Fin (dim N)) ℂ
  trace_eq : ∀ N, N₀ ≤ N → ∀ σ : Equiv.Perm (Fin N),
    (π N σ : Matrix (Fin (dim N)) (Fin (dim N)) ℂ).trace =
      MvPolynomial.eval (fun i : Fin r => ((xi ((i : ℕ) + 1) σ : ℕ) : ℂ)) φ

namespace StableRep

/-- `π_N` contains no copy of the trivial representation: no nonzero vector is fixed by every
`π_N(σ)`, for `N ≥ N₀`. -/
def NoTrivialSummand (π : StableRep) : Prop :=
  ∀ N, π.N₀ ≤ N → ∀ v : Fin (π.dim N) → ℂ,
    (∀ σ, (π.π N σ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) *ᵥ v = v) → v = 0

/-- `α`: the degree of `N ↦ D_N = ϕ(N, …, N)` as a polynomial in `N`. -/
def alpha (π : StableRep) : ℕ :=
  (MvPolynomial.aeval (fun _ : Fin π.r => (X : ℂ[X])) π.φ).natDegree

/-- `Πᴺ = (π_N(σ₁), …, π_N(σ_d))` as operators on `ℂ^{D_N}`. -/
def model (π : StableRep) {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    Fin d → EuclideanSpace ℂ (Fin (π.dim N)) →L[ℂ] EuclideanSpace ℂ (Fin (π.dim N)) :=
  fun i => Matrix.toEuclideanCLM (𝕜 := ℂ)
    (π.π N (σ i) : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ)

end StableRep

/-! ## Linearization (CGTvH Lemma 9.1) -/

/-- `X = ∑_{i=0}^{2d} Aᵢ ⊗ λ(gᵢ)` with `g₀ = e`, `g_{d+i} = gᵢ⁻¹` and `m × n` matrices `Aᵢ`. -/
def linOp {d m n : ℕ} (A : Letter d → Matrix (Fin m) (Fin n) ℂ) :
    PiLp 2 (fun _ : Fin n => L2Free d) →L[ℂ] PiLp 2 (fun _ : Fin m => L2Free d) :=
  ∑ l : Letter d, tensorOp (A l) (wordEval (sLimit d) [l])

/-- The product `X_t X_{t+1} ⋯ X_{t+k-1}` of linear operators `X_j = ∑ᵢ A_{j,i} ⊗ λ(gᵢ)`, where `A_{j,i}`
is a `D_j × D_{j+1}` matrix. -/
def linChain {d : ℕ} (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) (t : ℕ) :
    ∀ k : ℕ, PiLp 2 (fun _ : Fin (Dim (t + k)) => L2Free d) →L[ℂ]
      PiLp 2 (fun _ : Fin (Dim t) => L2Free d)
  | 0 => ContinuousLinearMap.id ℂ _
  | k + 1 => (linChain Dim A t k).comp (linOp (A (t + k)))

/-- Reindexing `n` copies of `H` as `m` copies along `Fin n ≃ Fin m`. -/
def reindexCopies {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n m : ℕ}
    (e : Fin n ≃ Fin m) : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin m => H) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H e).toContinuousLinearEquiv.toContinuousLinearMap

/-- `X₁ X₂ ⋯ X_q` as an operator on `D` copies of `ℓ²(F_d)`, when `D₁ = D_{q+1} = D`: the chain
`linChain Dim A 1 q` with its two end spaces identified with `D` copies through `finCongr`, which
is the identity on indices. -/
def linChainOn {d D : ℕ} (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) (q : ℕ)
    (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D) :
    PiLp 2 (fun _ : Fin D => L2Free d) →L[ℂ] PiLp 2 (fun _ : Fin D => L2Free d) :=
  (reindexCopies (finCongr h₁)).comp
    ((linChain Dim A 1 q).comp (reindexCopies (finCongr hq).symm))

end StrongConv

end


