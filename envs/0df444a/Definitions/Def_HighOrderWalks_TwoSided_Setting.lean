-- Prove2me | Definitions.Def_HighOrderWalks_TwoSided_Setting
-- name    : HighOrderWalks_TwoSided_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:19.145919+00:00
-- url     : https://prove2.me/theorems/2c4c7f00-9be0-4d44-8106-c7f663b2e325
-- title:
--   §2–§4, pp. 2, 6–13 — weighted pure complex, cochains, M⁺, M⁻, (M′)⁺, d, d*, links, two-sided local spectral expanders
-- statement:
--   This file fixes the objects of Kaufman–Oppenheim, *High Order Random Walks: Beyond Spectral Gap*, §2–§4.
--
--   **Complex.** A finite simplicial complex $X$ on a vertex type $V$ is a finite family of finite vertex sets, closed under taking subsets. A $k$-simplex ($k$-face) has $k+1$ vertices; $X(k)$ is the set of $k$-simplices and $X(-1)=\{\emptyset\}$. $X$ is **pure $n$-dimensional** if every face has at most $n+1$ vertices, every face is contained in a face with $n+1$ vertices, and $X$ is nonempty.
--
--   **Weight.** A weight function is $m : \bigcup_{-1\le k\le n} X(k)\to(0,\infty)$ such that for every $-1\le k\le n-1$ and $\tau\in X(k)$,
--   $$m(\tau)=\sum_{\sigma\in X(k+1),\ \tau\subseteq\sigma} m(\sigma).$$
--
--   **Cochains.** A $k$-cochain is a function $\phi : X(k)\to\mathbb R$, with the inner product $\langle\phi,\psi\rangle=\sum_{\sigma\in X(k)} m(\sigma)\phi(\sigma)\psi(\sigma)$ and the induced norm $\|\cdot\|$.
--
--   **Operators** (on $k$-cochains, $\tau\in X(k)$):
--   1. the signless differential $d\phi(\sigma)=\sum_{\tau\subset\sigma,\ \tau\in X(k)}\phi(\tau)$ for $\sigma\in X(k+1)$;
--   2. its adjoint, by the formula $d^*\psi(\tau)=\sum_{\sigma\in X(k+1),\ \tau\subset\sigma}\frac{m(\sigma)}{m(\tau)}\psi(\sigma)$;
--   3. the upper random walk $M^+_k\phi(\tau)=\frac{1}{k+2}\phi(\tau)+\sum_{\tau'\in X(k),\ \tau\cup\tau'\in X(k+1)}\frac{m(\tau\cup\tau')}{(k+2)m(\tau)}\phi(\tau')$;
--   4. the lower random walk $M^-_k\phi(\tau)=\Big(\sum_{\eta\in X(k-1),\ \eta\subset\tau}\frac{m(\tau)}{(k+1)m(\eta)}\Big)\phi(\tau)+\sum_{\tau'\ne\tau,\ \tau\cap\tau'\in X(k-1)}\frac{m(\tau')}{(k+1)m(\tau\cap\tau')}\phi(\tau')$;
--   5. the non-lazy upper walk $(M')^+_k=\frac{k+2}{k+1}M^+_k-\frac{1}{k+1}I$.
--
--   **Links.** For $\tau\in X$, the link is $X_\tau=\{\eta\in X:\ \eta\cap\tau=\emptyset,\ \tau\cup\eta\in X\}$, with weight $m_\tau(\eta)=m(\tau\cup\eta)$; the localization of a cochain is $\phi_\tau(\eta)=\phi(\tau\cup\eta)$. All the operators above are applied to $(X_\tau,m_\tau)$ unchanged. For $\tau\in X(k-1)$ the **link term** is
--   $$\sum_{\tau\in X(k-1)}\big\langle (M')^+_{\tau,0}(I-M^-_{\tau,0})\phi_\tau,\ \psi_\tau\big\rangle,$$
--   the inner products being those of $0$-cochains of $X_\tau$.
--
--   **Local spectral expansion.** Let $\mu_\tau$ be the second largest and $\nu_\tau$ the smallest eigenvalue of $(M')^+_{\tau,0}$. The predicate "$\max\{\mu_k,-\nu_k\}\le b$" says that for every $\tau\in X(k-1)$ and every $0$-cochain $g$ of $X_\tau$ with $\sum_v m_\tau(v)g(v)=0$,
--   $$\big|\langle (M')^+_{\tau,0}g,g\rangle\big|\le b\,\|g\|^2 .$$
--   $X$ is a **two-sided $\lambda$-local spectral expander** (Definition 1.2) if $-\lambda\le\nu_\tau$ and $\mu_\tau\le\lambda$ for every $\tau\in X(i)$, $-1\le i\le n-2$, i.e. the predicate holds with $b=\lambda$ for the links of all faces of dimension $-1,\dots,n-2$, including the empty face (whose link is $X$ itself).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Faces are finite sets `Finset V`, and $X(k)$ is `cells X (k + 1)`: faces are indexed by their number of vertices, so $X(-1)$ is `cells X 0`. Cochains are functions `Finset V → ℝ`; only their values on the relevant faces are read, and every operator is $0$ off $X$. The weight's codomain $\mathbb R^+$ is read as $(0,\infty)$ because $m$ appears in denominators. $d^*$ is defined by the formula of Lemma 3.6; that it is the adjoint of $d$ is the theorem `lemma_3_6`. The diagonal of $M^-_k$ is summed over $\eta\subset\tau$, which Definition 3.2 omits but the computation of $dd^*$ on p. 9 uses. The eigenvalue condition $\mu_k\le b$ is stated in its Rayleigh-quotient form on the $m_\tau$-orthogonal complement of the constants; by Courant–Fischer it is equivalent to the eigenvalue form, since $(M')^+_{\tau,0}$ is $m_\tau$-self-adjoint with the constants as an eigenvector of eigenvalue $1$, its largest eigenvalue; the absolute value covers both $\mu_\tau\le b$ and $-b\le\nu_\tau$. Definition 4.4 (p. 13) prints the two-sided clause as "$-\lambda\le\mu_k\le\lambda$", a misprint for Definition 1.2's "$-\lambda\le\nu_\tau,\ \mu_\tau\le\lambda$", which the proofs of §5.3 use; Definition 1.2 is followed.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, pp. 2, 6–13, Definition 1.2, §2 (pp. 6–7), Definitions 3.1–3.4 (pp. 7–8), Lemma 3.6 (p. 8), §4 (pp. 10–11), Definition 4.4 (p. 13)

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.TwoSided

/-- Definition 1.2, p. 2 and p. 11: `max{μ_c, -ν_c} ≤ b`, where `μ_τ` and `ν_τ` are the second
largest and the smallest eigenvalue of `(M')⁺_{τ,0}` and the bound is over all `τ ∈ X(c-1)`.
Stated in Rayleigh form: for every face `τ` with `c` vertices and every `g` on the vertices of the
HighOrderWalks.OneSided.link that is `m_τ`-orthogonal to the constants, `|⟨(M')⁺_{τ,0} g, g⟩| ≤ b ‖g‖²`. -/
def LinkTwoSided {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (b : ℝ) : Prop :=
  ∀ τ ∈ HighOrderWalks.OneSided.cells X c, ∀ g : Finset V → ℝ,
    HighOrderWalks.OneSided.ip (HighOrderWalks.OneSided.link X τ) (HighOrderWalks.OneSided.linkWeight m τ) 1 g (fun _ => 1) = 0 →
      |HighOrderWalks.OneSided.ip (HighOrderWalks.OneSided.link X τ) (HighOrderWalks.OneSided.linkWeight m τ) 1 (HighOrderWalks.OneSided.nonLazyWalk (HighOrderWalks.OneSided.link X τ) (HighOrderWalks.OneSided.linkWeight m τ) g) g| ≤
        b * HighOrderWalks.OneSided.ip (HighOrderWalks.OneSided.link X τ) (HighOrderWalks.OneSided.linkWeight m τ) 1 g g

/-- Definition 1.2, p. 2: `X` is a two-sided `λ`-local spectral expander if
`-λ ≤ ν_τ` and `μ_τ ≤ λ` for every `τ ∈ X(i)`, `-1 ≤ i ≤ n - 2` (including `τ = ∅`), i.e.
`LinkTwoSided X m c λ` for every `c = i + 1 ≤ n - 1`. (Definition 4.4, p. 13, misprints the
two-sided clause as `-λ ≤ μ_k ≤ λ`; Definition 1.2 is followed.) -/
def TwoSidedLSE {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (m : Finset V → ℝ) (n : ℕ)
    (lam : ℝ) : Prop :=
  ∀ c : ℕ, c + 1 ≤ n → LinkTwoSided X m c lam

end HighOrderWalks.TwoSided


