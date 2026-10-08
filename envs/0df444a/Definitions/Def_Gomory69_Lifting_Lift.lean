-- Prove2me | Definitions.Def_Gomory69_Lifting_Lift
-- name    : Gomory69_Lifting_Lift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:59:26.538162+00:00
-- url     : https://prove2.me/theorems/586f3b29-46a5-4be4-9bd0-3d1df77b3ae5
-- title:
--   Lifted coefficients π(g) = π′(ψg), pushed-forward paths τ, and the lifted paths T_k(τ) (pp. 486–487)
-- statement:
--   Let $\psi:\mathcal G\to\mathcal H$ be a homomorphism of finite Abelian groups, with kernel $\mathcal K=\psi^{-1}(\bar 0)$.
--
--   1. **Lifted coefficients.** For $\pi'$ indexed by $\mathcal H^+$, put $\pi(g)=\pi'(\psi g)$ for $g\in\mathcal G^+$, with $\pi'(\bar 0)=0$; thus $\pi(g)=0$ for $g\in\mathcal K$.
--   2. **Pushed-forward path.** For $t\in\mathbb N^{\mathcal G^+}$, put $\tau(h)=\sum_{g\in\psi^{-1}h}t(g)$ for $h\in\mathcal H^+$ (the sum runs over $g\in\mathcal G^+$ with $\psi g=h$).
--   3. **Lifted path.** Let $\phi:\mathcal H\to\mathcal G$ select coset representatives, $\psi\phi(h)=h$, let $k\in\mathcal K$ and $\tau\in\mathbb N^{\mathcal H^+}$. Every $g$ with $h=\psi g\ne\bar 0$ is written uniquely as $g=\phi(h)+k'$ with $k'\in\mathcal K$, and the path $T_k(\tau)=t_k$ has $t_k(g)=\tau(h)$ if $k'=k$ and $t_k(g)=0$ if $k'\neq k$. On the kernel, $t_k$ is $1$ at the single element
--   $$c = g_0-\sum_{g\notin\mathcal K}t_k(g)\cdot g$$
--   and $0$ at every other element of $\mathcal K\cap\mathcal G^+$.
--
--   The lifted coefficients are the inequality of THEOREM 19; the other two constructions translate paths between the two group problems in its proof.
--
--   **Formalization Note** `liftCoeff ψ π' g = ext π' (ψ g)`. `liftedPathBase` is the part of $t_k$ off the kernel and `closingElement` is $c$. When $c=\bar 0$ nothing is added, since $\bar 0$ has no coordinate. The page writes the kernel part as "$g=\phi(h)+k'$ with $h=\bar 0$ and $k'=c$", which places the $1$ on $\phi(\bar 0)+c$; the Lean places it on $c$ itself, which agrees with the page when $\phi(\bar 0)=\bar 0$ (the page's Fig. 6 labels the kernel columns by $\mathcal K$) and is the reading under which $T_k(\tau)$ solves the group equation for any section $\phi$.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 486 (THEOREM 19, π(g) = π′(ψg), τ(h) = Σ t(g)), p. 487 (t_k(g), T_k(τ))

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron

namespace Gomory69.Lifting

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- The lifted coefficients of THEOREM 19: `π(g) = π′(ψ g)` for `g ∈ 𝒢⁺`, with `π′(0̄) = 0`,
so `π(g) = 0` on the kernel of `ψ`. -/
def liftCoeff [DecidableEq H] (ψ : G →+ H) (π' : Plus H → ℝ) : Plus G → ℝ :=
  fun g => ext π' (ψ g)

/-- Pushing a path forward along `ψ` (proof of THEOREM 19, p. 486):
`τ(h) = ∑_{g ∈ ψ⁻¹ h} t(g)` for `h ∈ ℋ⁺`. -/
def pushForward [Fintype G] [DecidableEq G] [DecidableEq H] (ψ : G →+ H)
    (t : Plus G → ℕ) : Plus H → ℕ :=
  fun h => ∑ g ∈ Finset.univ.filter (fun g : Plus G => ψ (g : G) = (h : H)), t g

/-- The non-kernel part of the lifted path `T_k(τ)` (p. 487): for `g ∈ 𝒢⁺` with `ψ g = h ≠ 0̄`,
written `g = φ(h) + k′`, it is `τ(h)` if `k′ = k` and `0` otherwise; it is `0` on the kernel. -/
def liftedPathBase [DecidableEq G] [DecidableEq H] (ψ : G →+ H) (φ : H → G) (k : G)
    (τ : Plus H → ℕ) : Plus G → ℕ :=
  fun g => if hg : ψ (g : G) = 0 then 0
    else if (g : G) = φ (ψ (g : G)) + k then τ ⟨ψ (g : G), hg⟩ else 0

/-- The kernel element that closes the lifted path: `g₀ − ∑_{g ∉ 𝒦} t_k(g) · g`. -/
def closingElement [Fintype G] [DecidableEq G] [DecidableEq H] (ψ : G →+ H) (φ : H → G)
    (g₀ k : G) (τ : Plus H → ℕ) : G :=
  g₀ - ∑ g : Plus G, liftedPathBase ψ φ k τ g • (g : G)

/-- The lifted path `T_k(τ)` of p. 487: the non-kernel part `liftedPathBase`, plus a single `1` on
the closing kernel element `g₀ − ∑_{g ∉ 𝒦} t_k(g) · g` when that element is nonzero (when it is
`0̄`, nothing is added, since `t` has no `0̄` coordinate). -/
def liftedPath [Fintype G] [DecidableEq G] [DecidableEq H] (ψ : G →+ H) (φ : H → G)
    (g₀ k : G) (τ : Plus H → ℕ) : Plus G → ℕ :=
  fun g => liftedPathBase ψ φ k τ g +
    if (g : G) = closingElement ψ φ g₀ k τ then 1 else 0

end Gomory69.Lifting


