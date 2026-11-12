-- Prove2me | Definitions.Def_FourMsgQMA_Arg4_Complete
-- name    : FourMsgQMA_Arg4_Complete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:37:12.962291+00:00
-- url     : https://prove2.me/theorems/c454e2df-e704-4c74-9db0-3050efb5c683
-- title:
--   Overwhelming completeness for every honest resource
-- statement:
--   An argument $\Pi$ is **overwhelmingly complete** for $(L,F)$ if for every polynomial bound $B$ there is a negligible $\nu$ with the following property. For every $\lambda$, every admissible $u=(C,X)$ with $|u|\le B(\lambda)$, every $y$ with $C(y)=1$ and $x_i\in L_{\mathrm{yes}}$ whenever $y_i=1$, and every family of density operators $\rho_i\in W_Q(x_i,2/3)$ at the selected coordinates,
--   $$
--   \Pr\big[\Pi\text{ accepts in the honest execution with }(y,a)\text{ and }\textstyle\bigotimes_{i:y_i=1}\rho_i^{\otimes N}\big]\ \ge\ 1-\nu(\lambda).
--   $$
--   Such a $y$ exists exactly when $X\in L^C_{\mathrm{yes}}$. So this is §3.3's "for every admissible $u\in L_{\mathrm{yes}}$ and every $\omega\in W_\Pi(u)$", with the resource set of p.10 and p.36.
--
--   **Formalization Note** Pinned-down version (operator request). The honest resource is fixed by the statement (threshold $2/3$, the scheme's polynomial copy count $N$, mixed witnesses allowed), and completeness must hold for every such resource.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.3, p.11 (PDF 13); Definition 3.1, p.10; §3.2, pp.9–10; §5.1, p.36 (PDF 38)

import Mathlib
import Definitions.Def_FourMsgQMA_Arg4

namespace FourMsgQMA

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- Overwhelming completeness for every honest resource (§3.3, p.11; Definition 3.1, p.10; §3.2,
pp.9–10; §5.1, p.36). For every polynomial bound `B` on the instance size there is a negligible
`ν` such that, for every `λ`, every admissible instance `u = (C, X)` with `|u| ≤ B(λ)`, every
authorized `y` (`C(y) = 1`) that selects only yes-instances (`y_i = 1 ⇒ x_i ∈ L_yes`), and every
choice of witness density operators `ρ_i ∈ W_Q(x_i, 2/3)` at the selected coordinates, the honest
execution with the classical witness `(y, a)` and the quantum resource
`⊗_{i : y_i = 1} ρ_i^{⊗N(λ, t(X))}` accepts with probability at least `1 − ν(λ)`.

Such a `y` exists exactly when `X ∈ L^C_yes` (Definition 3.1), so this is "for every admissible
`u ∈ L_yes` and every `ω ∈ W_Π(u)`" with `W_Π(u)` the resource set of p.10 and p.36.

**Formalization Note** Pinned-down version (operator request): the threshold is the QMA
threshold `2/3` of p.10, the witnesses may be mixed, the copy count `N` is chosen by the scheme
(`Arg4.copies`), and completeness is required for every resource of this form. -/
def Arg4.Complete (A : Arg4) (L : PromiseProblem) (F : QMAFamily) : Prop :=
  ∀ B : ℕ → ℕ, PolyBound B → ∃ ν : ℕ → ℝ, Negligible ν ∧
    ∀ (lam : ℕ) (u : Inst), u.Admissible → u.size ≤ B lam →
    ∀ y : Fin u.k → Bool, u.C.eval y = true → (∀ i, y i = true → u.X i ∈ L.yes) →
    ∀ ρ : (i : Fin u.k) → Matrix (Qubits (witWidth F u i)) (Qubits (witWidth F u i)) ℂ,
      (∀ i, y i = true → ρ i ∈ WQ F (u.X i) (2 / 3)) →
      1 - ν lam ≤ A.honestAccept F lam u y ρ

end FourMsgQMA


