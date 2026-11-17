-- Prove2me | Definitions.Def_DirTeleMC_Supplement_LPFeasible
-- name    : DirTeleMC_Supplement_LPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:40:37.347721+00:00
-- url     : https://prove2.me/theorems/633605dd-bcd3-4a8d-989f-b6d0bf0fd5fc
-- title:
--   The linear program LP($\theta$)
-- statement:
--   Let $\theta\ge1$. Let $V_{\le\theta}$ be the set of vertices $v$ with $\mathrm{dist}(s,v)\le\theta$, let $G_{\le\theta}$ be the subdigraph of $G$ induced by $V_{\le\theta}$ with the arcs into $s$ deleted, and for a terminal $t$ let $\mathcal P_t$ be the set of directed paths from $s$ to $t$ in $G_{\le\theta}$ with at most $\theta$ arcs. If $K\subseteq V_{\le\theta}$, the linear program LP($\theta$) has variables $x_e\ge0$ for the arcs $e$ of $G_{\le\theta}$ and $f^t_P\ge0$ for $t\in K$, $P\in\mathcal P_t$, and the constraints
--   $$\sum_{P\in\mathcal P_t}f^t_P=1\ (t\in K),\qquad \sum_{P\in\mathcal P_t:\,e\in P}f^t_P\le x_e\ (t\in K,\ e\in E(G_{\le\theta})),\qquad \sum_{e\text{ leaving }v}x_e\le\theta\ (v\in V_{\le\theta}).$$
--   It has no objective; if $K\not\subseteq V_{\le\theta}$ it is called infeasible. The predicate $\mathrm{LPFeasible}(\theta,x)$ says that some $f$ makes $(x,f)$ feasible.
--
--   LP($\theta$) guides the separator choices of LPSEP, which runs it at the least feasible guess $\theta$.
--
--   **Formalization Note** $x$ is a function on ordered vertex pairs, of which only the arcs of $G_{\le\theta}$ matter; the path flow $f^t$ is a finitely supported function on vertex lists, supported on $\mathcal P_t$.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), App. C.2 and Definition C.1, p.38 (PDF p.39)

import Mathlib
import Definitions.Def_DirTeleMC_Inst

namespace DirTeleMC.Supplement

open DirTeleMC

/-- `V_{≤θ}` (App. C.2, p.38: "let V≤θ be the set of vertices v with dist(s, v) ≤ θ"): the vertices reached from `s`
by a walk with at most `θ` arcs. -/
noncomputable def VLe (I : Inst) (θ : ℕ) : Finset (Fin I.n) := by
  classical
  exact Finset.univ.filter fun v => HopReach I.adj θ I.s v

/-- The arcs of `G_{≤θ}` (App. C.2, p.38: "let G≤θ be the subdigraph of G induced by V≤θ, with the arcs into s
deleted"). -/
def ArcLe (I : Inst) (θ : ℕ) (u v : Fin I.n) : Prop :=
  I.adj u v = true ∧ u ∈ VLe I θ ∧ v ∈ VLe I θ ∧ v ≠ I.s

/-- `P ∈ P_t` (App. C.2, p.38: "the set of directed paths from s to t in G≤θ with at most θ arcs"), with paths as
vertex lists without repetition. -/
def IsLPPath (I : Inst) (θ : ℕ) (t : Fin I.n) (P : List (Fin I.n)) : Prop :=
  P.head? = some I.s ∧ P.getLast? = some t ∧ P.Nodup ∧ P.IsChain (ArcLe I θ) ∧ P.length ≤ θ + 1

/-- **`(x, f)` is feasible for LP(θ)** (Definition C.1, p.38).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…): "For an integer θ ≥ 1 with K ⊆ V≤θ, the linear program LP(θ) has a variable xe ≥ 0
for every arc e of G≤θ and a variable f^t_P ≥ 0 for every terminal t and every path P ∈ Pt, and the constraints
Σ_{P∈Pt} f^t_P = 1 (t ∈ K), Σ_{P∈Pt : e∈P} f^t_P ≤ xe (t ∈ K, e ∈ E(G≤θ)), Σ_{e∈E(G≤θ) leaving v} xe ≤ θ
(v ∈ V≤θ). It has no objective. If K ⊄ V≤θ, we call LP(θ) infeasible."

`LPFeasible I θ x`: `K ⊆ V_{≤θ}`, `x ≥ 0` on the arcs of `G_{≤θ}`, and some path flow `f` (a finitely supported
nonnegative weight `f t P` on the paths `P ∈ P_t`) satisfies the three families of constraints.

**Formalization Note.** `x` is a function on all ordered pairs; only its values on the arcs of `G_{≤θ}` enter. An
arc `(u, v)` lies on `P` when `u, v` are consecutive in `P`. -/
noncomputable def LPFeasible (I : Inst) (θ : ℕ) (x : Fin I.n → Fin I.n → ℝ) : Prop := by
  classical
  exact I.K ⊆ VLe I θ ∧ (∀ u v, ArcLe I θ u v → 0 ≤ x u v) ∧
    ∃ f : Fin I.n → List (Fin I.n) →₀ ℝ,
      (∀ t P, 0 ≤ f t P) ∧ (∀ t P, f t P ≠ 0 → IsLPPath I θ t P) ∧
      (∀ t ∈ I.K, (f t).sum (fun _ a => a) = 1) ∧
      (∀ t ∈ I.K, ∀ u v, ArcLe I θ u v →
        (∑ P ∈ (f t).support.filter (fun P => (u, v) ∈ P.zip P.tail), f t P) ≤ x u v) ∧
      ∀ v ∈ VLe I θ, (∑ w ∈ Finset.univ.filter (fun w => ArcLe I θ v w), x v w) ≤ θ

end DirTeleMC.Supplement


