-- Prove2me | Definitions.Def_QuadBogolyubov_HasRankAtLeast
-- name    : QuadBogolyubov_HasRankAtLeast
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:42.243801+00:00
-- url     : https://prove2.me/theorems/0460e897-6b59-41b9-b0e2-05fe1773952f
-- title:
--   Bilinear form $B_q$, rank $\mathrm{rk}_V(q)$ and the lower bound $\mathrm{rk}(W)\ge r$
-- statement:
--   For $q:E\to\mathbb F_2$ on an $\mathbb F_2$-module $E$, the associated form is
--   $$B_q(u,v)=q(u+v)+q(u)+q(v)+q(0).$$
--   The **rank** of a form $b$ is the dimension of the span of the functionals $b(u,\cdot)$, which equals $\dim E-\dim\operatorname{rad}(b)$. The rank $\mathrm{rk}_V(q)$ of $q$ on $V$ is the rank of $B_q$ on $V_0=V+V$, and the statement $\mathrm{rk}(W)\ge r$ means
--   $$r\le\mathrm{rk}_V(\lambda_1q_1+\dots+\lambda_{d_2}q_{d_2})\quad\text{for every }\lambda\in\mathbb F_2^{d_2}\setminus\{0\}.$$
--   High rank is the hypothesis under which a quadratic variety behaves like a generic set of its density.
--
--   **Formalization Note** The base point of the second derivative is $0$; for a quadratic polynomial on $\mathbb F_2^n$ the derivative $\partial_u\partial_vq(x)$ does not depend on $x$, so this is the paper's form (2). Rank is stated as a lower bound so that $d_2=0$ gives infinite rank, the convention of p.68: then $\mathrm{rk}(W)\ge r$ holds for every real $r$.
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), eq. (2), p.9; Definition 3.1, pp.9–10; App. D, p.52; p.68

import Mathlib
import Definitions.Def_QuadBogolyubov_QuadVariety

set_option autoImplicit false

namespace QuadBogolyubov

/-- The **bilinear form associated with a function** `q : E → 𝔽₂` on an additive group `E`:
`B_q(u, v) = ∂_u ∂_v q(0) = q(u + v) + q(u) + q(v) + q(0)`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), §3, p.9,
eq. (2): "Bq(u, v) := ∂u∂vq(x) = q(x + u + v) + q(x + u) + q(x + v) + q(x), where x ∈ V is an
arbitrary element."

**Formalization Note.** The base point is `x = 0`. For a quadratic polynomial on `𝔽₂ⁿ` the
second derivative `∂_u∂_v q(x)` does not depend on `x ∈ 𝔽₂ⁿ`, so this is the paper's form for
every base point `x ∈ V`. -/
def bilin {E : Type} [Add E] [Zero E] (q : E → ZMod 2) (u v : E) : ZMod 2 :=
  q (u + v) + q u + q v + q 0

/-- The **rank** of a bilinear form `b` on an `𝔽₂`-module `E`: the dimension of the span of the
functionals `b(u, ·)`, `u ∈ E`, i.e. the rank of the map `T : u ↦ b(u, ·)`, equivalently
`dim E − dim rad(b)` (App. D, p.52: "its rank is the rank of the linear map Tq : G → G∗ defined
by h ↦ βq(h, ·). Thus rk(βq) = dim G − dim rad(βq)"). -/
noncomputable def bilinRank {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (b : E → E → ZMod 2) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range b))

/-- `rk_V(q)`: the rank of the bilinear form `B_q` restricted to `V₀ = V + V` (Definition 3.1,
p.9: "The rank of q on V, denoted rkV(q), is the rank of its associated bilinear form Bq on
V0 = V + V"). -/
noncomputable def rkOn {n : ℕ} (W : QuadVariety n) (q : (Fin n → ZMod 2) → ZMod 2) : ℕ :=
  bilinRank (fun u v : W.dir => bilin q (u : Fin n → ZMod 2) (v : Fin n → ZMod 2))

/-- `rk(W) ≥ r`: for every `λ ∈ 𝔽₂^{d₂} \ {0}`, `rk_V(λ₁q₁ + ⋯ + λ_{d₂}q_{d₂}) ≥ r`.

Definition 3.1, pp.9–10: "rk(W) = min_{(λ1,...,λd)∈F₂ᵈ\{0}} rkV(λ1q1 + · · · + λdqd)".

**Formalization Note.** The rank is a property of the representation. It is stated as a lower
bound so that `d₂ = 0` (a minimum over the empty set) gives infinite rank, the paper's convention
(p.68: "When q = 0, we say by convention that the rank is infinite"): then `HasRankAtLeast W r`
holds for every `r`. -/
def HasRankAtLeast {n : ℕ} (W : QuadVariety n) (r : ℝ) : Prop :=
  ∀ lam : Fin W.d2 → ZMod 2, lam ≠ 0 →
    r ≤ (rkOn W (fun x => ∑ j, lam j * W.q j x) : ℝ)

end QuadBogolyubov


