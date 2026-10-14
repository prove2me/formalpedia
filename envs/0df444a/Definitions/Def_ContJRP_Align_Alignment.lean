-- Prove2me | Definitions.Def_ContJRP_Align_Alignment
-- name    : ContJRP_Align_Alignment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:58.086811+00:00
-- url     : https://prove2.me/theorems/9496fe87-22f2-4375-845d-7316c262c911
-- title:
--   §2.3–2.5, pp. 7–11 — L, Ψ, segments, active set, representatives, Ψ-alignment, α, the alignment graph, (LP), misalignment
-- statement:
--   Fix $\epsilon\in(0,\tfrac12)$, a reference policy $T^*=(T^*_1,\dots,T^*_n)$ and an estimate $\tilde T_{\min}>0$ of its minimal interval.
--
--   1. **Segments.** $L$ is the least natural number with $(1+\epsilon)^L>1/\epsilon$, and for $\ell=1,\dots,L$
--   $$S_\ell=\big[(1+\epsilon)^{\ell-1}\tilde T_{\min},\ (1+\epsilon)^{\ell}\tilde T_{\min}\big),\qquad \bar S_\ell=\big[(1+\epsilon)^{\ell-1}\tilde T_{\min},\ (1+\epsilon)^{\ell}\tilde T_{\min}\big].$$
--   The constant $\Psi=2L^2\cdot2^L/\epsilon$.
--
--   2. **Active segments and representatives.** $S_\ell$ is **active** when some $T^*_i\in S_\ell$; $\mathcal A^*\subseteq[L]$ is the set of active segments. A **choice of representatives** assigns to each active $S_\ell$ one interval $R^*_\ell=T^*_i$ lying in $S_\ell$.
--
--   3. **$\Psi$-alignment.** Two reals $x,y$ are **$\Psi$-aligned** when $a x=b y$ for some positive integers $a,b\le\Psi$; equivalently, the least common multiple $M$ of $x,y$ exists and $M/x,M/y\le\Psi$. For active $\ell_1,\ell_2$ with $\Psi$-aligned representatives, $\alpha_{\{\ell_1,\ell_2\},\ell_1}=M/R^*_{\ell_1}$ and $\alpha_{\{\ell_1,\ell_2\},\ell_2}=M/R^*_{\ell_2}$.
--
--   4. **Alignment graph.** $G^*_\Psi=(\mathcal A^*,\mathcal P^*_\Psi)$ joins two distinct active segments when their representatives are $\Psi$-aligned; $\mathrm{CC}(G^*_\Psi)$ is its set of connected components.
--
--   5. **The program (LP).** A vector $(R_\ell)_{\ell\in\mathcal A^*}$ is feasible for (LP) when
--   $$\text{(A) } R_\ell\in\bar S_\ell\ \ \forall\ell\in\mathcal A^*,\qquad \text{(B) }\alpha_{\{\ell_1,\ell_2\},\ell_1}R_{\ell_1}=\alpha_{\{\ell_1,\ell_2\},\ell_2}R_{\ell_2}\ \ \forall(\ell_1,\ell_2)\in\mathcal P^*_\Psi .$$
--   (LP$_C$) is the same system restricted to the segments of a set $C$ and to the edges inside $C$.
--
--   6. **Misalignment.** $x,y$ are **misaligned** when $a x\ne b y$ for all positive integers $a,b\le\Psi$. A vector $R$ is **cross-misaligned** when $R_{\ell_1},R_{\ell_2}$ are misaligned whenever $\ell_1,\ell_2$ lie in different components of $G^*_\Psi$.
--
--   7. **(Un)crossing sets.** A nonempty $\mathcal A\subseteq\mathcal A^*$ is **uncrossing** when it lies inside one component of $G^*_\Psi$, and **crossing** otherwise.
--
--   These are the objects of the Ψ-pairwise alignment algorithm of §2.
--
--   **Formalization Note** Segments are indexed from $0$ in Lean: Lean's `seg ε Tt ℓ` is the paper's $S_{\ell+1}$, so the paper's $R_1$ is `R 0`. The page leaves $L$ as $O(\tfrac1\epsilon\log\tfrac1\epsilon)$; the least $L$ with $(1+\epsilon)^L>1/\epsilon$ is the choice for which the half-open segments cover $[\tilde T_{\min},\tilde T_{\min}/\epsilon]$ including its right endpoint. The page says "integers $\alpha_1\le\Psi$ and $\alpha_2\le\Psi$"; the multiples are taken positive, since $\alpha_1=\alpha_2=0$ would make misalignment unsatisfiable. The multiples $\alpha$ are computed from $R^*$ with `alignMult`, the least positive $a$ with $a x=b y$ for a positive integer $b$. Vectors are functions $\mathbb N\to\mathbb R$, of which only the active coordinates matter; components are the reachability classes of $G^*_\Psi$ inside $\mathcal A^*$.
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, pp. 7–11, §2.3 (segments, A*, R*), §2.4 (Ψ-alignment, α, (LP)), §2.5 (G*_Ψ, (LP_C), misalignment); p. 13 (uncrossing sets)

import Mathlib
import Definitions.Def_ContJRP_Align_Model

namespace ContJRP.Align

open Classical

/-- The number of segments `L`: the least `L ∈ ℕ` with `(1 + ε)^L > 1/ε`, so that the half-open
segments `S_1, …, S_L` cover `[T̃_min, T̃_min/ε]` including its right endpoint (§2.3, p. 8). -/
noncomputable def numSegments (ε : ℝ) : ℕ :=
  sInf {L : ℕ | 1 / ε < (1 + ε) ^ L}

/-- The alignment bound `Ψ = 2 L² 2^L / ε` (§2.4, pp. 8–9). -/
noncomputable def Psi (ε : ℝ) : ℝ :=
  2 * (numSegments ε : ℝ) ^ 2 * 2 ^ numSegments ε / ε

/-- The segment `S_{ℓ+1} = [(1+ε)^ℓ T̃_min, (1+ε)^{ℓ+1} T̃_min)` (0-based Lean index `ℓ`; the
paper's `S_ℓ` is Lean index `ℓ - 1`). -/
def seg (ε Tt : ℝ) (ℓ : ℕ) : Set ℝ :=
  Set.Ico ((1 + ε) ^ ℓ * Tt) ((1 + ε) ^ (ℓ + 1) * Tt)

/-- The closed segment `S̄_{ℓ+1} = [(1+ε)^ℓ T̃_min, (1+ε)^{ℓ+1} T̃_min]` used in (LP). -/
def segClosed (ε Tt : ℝ) (ℓ : ℕ) : Set ℝ :=
  Set.Icc ((1 + ε) ^ ℓ * Tt) ((1 + ε) ^ (ℓ + 1) * Tt)

/-- The index set `A*` of active segments: those `ℓ < L` containing some `T*_i` (§2.3, p. 8). -/
noncomputable def active {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) : Finset ℕ :=
  (Finset.range (numSegments ε)).filter (fun ℓ => ∃ i, Tstar i ∈ seg ε Tt ℓ)

/-- `Rstar` is a choice of representatives: for every active segment, `R*_ℓ` is one of the
intervals `T*_i` lying in that segment (§2.3, p. 8). -/
def IsRepChoice {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar : ℕ → ℝ) : Prop :=
  ∀ ℓ ∈ active ε Tt Tstar, ∃ i, Rstar ℓ = Tstar i ∧ Tstar i ∈ seg ε Tt ℓ

/-- `x` and `y` are `Ψ`-aligned: `a x = b y` for some positive integers `a, b ≤ Ψ`. Equivalently,
the least-common-multiple multiples `M/x` and `M/y` are both at most `Ψ` (§2.4, p. 8). -/
def PsiAligned (Ψ x y : ℝ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ (a : ℝ) ≤ Ψ ∧ 0 < b ∧ (b : ℝ) ≤ Ψ ∧ (a : ℝ) * x = b * y

/-- The least positive integer `a` with `a x = b y` for some positive integer `b`; for commensurable
`x, y > 0` this is `M/x`, `M` the least common multiple. `α_{{ℓ₁,ℓ₂},ℓ₁} = alignMult R*_{ℓ₁} R*_{ℓ₂}`. -/
noncomputable def alignMult (x y : ℝ) : ℕ :=
  sInf {a : ℕ | 0 < a ∧ ∃ b : ℕ, 0 < b ∧ (a : ℝ) * x = b * y}

/-- The alignment graph `G*_Ψ` on the active segments: an edge joins two distinct active segments
whose representatives are `Ψ`-aligned (§2.5, p. 9). Vertices outside `A*` are isolated. -/
noncomputable def alignGraph {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar : ℕ → ℝ) :
    SimpleGraph ℕ :=
  SimpleGraph.fromRel (fun ℓ₁ ℓ₂ => ℓ₁ ∈ active ε Tt Tstar ∧ ℓ₂ ∈ active ε Tt Tstar ∧
    PsiAligned (Psi ε) (Rstar ℓ₁) (Rstar ℓ₂))

/-- Feasibility of `R` for the program (LP) restricted to the segments of `C`, i.e. (LP_C):
(A) `R_ℓ ∈ S̄_ℓ` for `ℓ ∈ C`, and (B) `α_{{ℓ₁,ℓ₂},ℓ₁} R_{ℓ₁} = α_{{ℓ₁,ℓ₂},ℓ₂} R_{ℓ₂}` for every
`Ψ`-aligned pair with `ℓ₁, ℓ₂ ∈ C` (pp. 9–10). -/
def IsLPFeasibleOn {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar : ℕ → ℝ) (C : Finset ℕ)
    (R : ℕ → ℝ) : Prop :=
  (∀ ℓ ∈ C, R ℓ ∈ segClosed ε Tt ℓ) ∧
    ∀ ℓ₁ ∈ C, ∀ ℓ₂ ∈ C, (alignGraph ε Tt Tstar Rstar).Adj ℓ₁ ℓ₂ →
      (alignMult (Rstar ℓ₁) (Rstar ℓ₂) : ℝ) * R ℓ₁ = (alignMult (Rstar ℓ₂) (Rstar ℓ₁) : ℝ) * R ℓ₂

/-- Feasibility of `R` for the program (LP) over all active segments (p. 9). -/
def IsLPFeasible {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar : ℕ → ℝ) (R : ℕ → ℝ) : Prop :=
  IsLPFeasibleOn ε Tt Tstar Rstar (active ε Tt Tstar) R

/-- `x` and `y` are misaligned: `a x ≠ b y` for all positive integers `a, b ≤ Ψ` (p. 10). -/
def Misaligned (Ψ x y : ℝ) : Prop :=
  ∀ a b : ℕ, 0 < a → (a : ℝ) ≤ Ψ → 0 < b → (b : ℝ) ≤ Ψ → (a : ℝ) * x ≠ b * y

/-- Every pair of representatives `R_{ℓ₁}, R_{ℓ₂}` in different components of `G*_Ψ` is
misaligned (Lemma 2.5, p. 11). -/
def CrossMisaligned {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar : ℕ → ℝ) (R : ℕ → ℝ) :
    Prop :=
  ∀ ℓ₁ ∈ active ε Tt Tstar, ∀ ℓ₂ ∈ active ε Tt Tstar,
    ¬ (alignGraph ε Tt Tstar Rstar).Reachable ℓ₁ ℓ₂ → Misaligned (Psi ε) (R ℓ₁) (R ℓ₂)

/-- The connected components `CC(G*_Ψ)`, each as the finite set of its active segments. -/
noncomputable def components {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar : ℕ → ℝ) :
    Finset (Finset ℕ) :=
  (active ε Tt Tstar).image
    (fun ℓ => (active ε Tt Tstar).filter (fun ℓ' => (alignGraph ε Tt Tstar Rstar).Reachable ℓ ℓ'))

/-- A set of segments `A ⊆ A*` is uncrossing when it is nonempty and contained in a single
connected component of `G*_Ψ` (§3.1, p. 13). -/
def IsUncrossing {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar : ℕ → ℝ) (A : Finset ℕ) : Prop :=
  A.Nonempty ∧ ∀ ℓ₁ ∈ A, ∀ ℓ₂ ∈ A, (alignGraph ε Tt Tstar Rstar).Reachable ℓ₁ ℓ₂

end ContJRP.Align


