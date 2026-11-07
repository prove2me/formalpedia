-- Prove2me | Definitions.Def_DiagLinesLDT_reducedAcc
-- name    : DiagLinesLDT_reducedAcc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:52:46.960199+00:00
-- url     : https://prove2.me/theorems/12ea3b4e-65c0-4ce3-a08b-f1c35589d7b4
-- title:
--   Acceptance of the reduced low-individual-degree test, and consistency with a global measurement
-- statement:
--   Write $\langle\psi|M\otimes N|\psi\rangle$ for the expectation with Alice's operator on the left, and $\mathbb E$ for a uniform average. For a strategy with point families $A^{w,u}$ and line families $B^{w,\ell}$:
--
--   1. the **axis-parallel lines test** (Definition 2.1) chooses a player $w$ uniformly, $u$ and $i$ independently and uniformly, sends the line through $u$ in direction $e_i$ to $w$ and the point $u$ to the other player, and accepts exactly when $f(u)=a$;
--   2. the **self-consistency test** (Definition 2.2) sends a uniform $u$ to both players and accepts exactly when $a=b$;
--   3. the **reduced test** (Definition 2.3) chooses one of the two with probability $1/2$ each; the diagonal-lines test is omitted.
--
--   The **consistency** of a measurement $G=\{G_g\}$ on Bob's space, with outcomes functions $g:\mathbb F_q^m\to\mathbb F_q$, is
--
--   $$\mathbb E_{u}\sum_{a\in\mathbb F_q}\sum_{g:\,g(u)=a}\langle\psi|A^{u}_a\otimes G_g|\psi\rangle,$$
--
--   with $A^u=A^{\mathrm{Alice},u}$.
--
--   **Formalization Note** Expectations are real parts; for tensors of Hermitian operators the value is already real. An average over an empty type is $0$; only nonempty types occur in the mission. $G$ is indexed by all functions, and zero operators are allowed, so a measurement with outcomes in a subset of the functions is a special case.
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Definitions 2.1, 2.2, 2.3, pp.4–5, and Theorem 3.1, p.5

import Mathlib
import Definitions.Def_DiagLinesLDT_Strategy

open scoped Kronecker

namespace DiagLinesLDT

/-- The uniform average `𝔼_{a∼α} f(a)`.

**Formalization Note** On an empty `α` this is `0 / 0 = 0`. Every average of the mission over points
or coordinates runs over a nonempty type (`m = 2`, `F` a field). -/
noncomputable def uniformAvg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / (Fintype.card α : ℝ)

/-- The expectation `⟨ψ| M ⊗ N |ψ⟩`, Alice's operator on the left.

**Formalization Note** The real part is taken. Every expectation of the mission is of a tensor of
Hermitian operators, hence already real, so no information is lost. -/
noncomputable def expect {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ψ : ι × κ → ℂ) (M : Matrix ι ι ℂ) (N : Matrix κ κ ℂ) : ℝ :=
  (star ψ ⬝ᵥ ((M ⊗ₖ N).mulVec ψ)).re

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}
  {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]

/-- Acceptance probability of the **axis-parallel lines test** (Definition 2.1, p.4): `w` is uniform in
`{Alice, Bob}`; `u` and `i` are independent and uniform; the line `ℓ` through `u` in direction `e_i` goes
to `w`, who returns `f`; the point `u` goes to the other player, who returns `a`; the verifier accepts
exactly when `f(u) = a`. Each orientation uses that player's own families.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Definition 2.1, p.4. -/
noncomputable def axisAcc (S : Strategy F m d ιA ιB) : ℝ :=
  (1 / 2) * uniformAvg (fun u : Fin m → F => uniformAvg fun i : Fin m =>
      ∑ f : LegalAnswer d (lineOf u i), ∑ a : F,
        if f.1 ⟨u, self_mem_lineThrough u i⟩ = a then
          expect S.state (S.lineA (lineOf u i) f) (S.pointB u a) else 0)
    + (1 / 2) * uniformAvg (fun u : Fin m → F => uniformAvg fun i : Fin m =>
      ∑ f : LegalAnswer d (lineOf u i), ∑ a : F,
        if f.1 ⟨u, self_mem_lineThrough u i⟩ = a then
          expect S.state (S.pointA u a) (S.lineB (lineOf u i) f) else 0)

/-- Acceptance probability of the **self-consistency test** (Definition 2.2, p.4): `u` is uniform and
goes to both players; Alice returns `a`, Bob returns `b`; the verifier accepts exactly when `a = b`. -/
noncomputable def selfAcc (S : Strategy F m d ιA ιB) : ℝ :=
  uniformAvg fun u : Fin m → F => ∑ a : F, ∑ b : F,
    if a = b then expect S.state (S.pointA u a) (S.pointB u b) else 0

/-- Acceptance probability of the **reduced low-individual-degree test** (Definition 2.3, p.5): the
axis-parallel lines test or the self-consistency test, each with probability `1/2`. The diagonal-lines
test is omitted. -/
noncomputable def reducedAcc (S : Strategy F m d ιA ιB) : ℝ :=
  (1 / 2) * axisAcc S + (1 / 2) * selfAcc S

/-- The consistency of a global measurement `G` on Bob's space with Alice's point measurements:
`𝔼_u Σ_a Σ_{g : g(u) = a} ⟨ψ| A^u_a ⊗ G_g |ψ⟩` (Theorem 3.1, p.5).

**Formalization Note** `G` is indexed by all functions `𝔽_q^m → 𝔽_q`. Zero operators are allowed, so a
measurement with outcomes in a subset of the functions is the special case that is zero elsewhere. -/
noncomputable def consistency (S : Strategy F m d ιA ιB)
    (G : ((Fin m → F) → F) → Matrix ιB ιB ℂ) : ℝ :=
  uniformAvg fun u : Fin m → F => ∑ a : F, ∑ g : (Fin m → F) → F with g u = a,
    expect S.state (S.pointA u a) (G g)

end DiagLinesLDT


