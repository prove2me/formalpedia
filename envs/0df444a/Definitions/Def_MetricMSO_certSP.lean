-- Prove2me | Definitions.Def_MetricMSO_certSP
-- name    : MetricMSO_certSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:31.976559+00:00
-- url     : https://prove2.me/theorems/b5929841-93a5-4626-970a-aa070fd21adf
-- title:
--   The shortest-path certificate $\mathsf{CertSP}_M(P,s,t)$, eq. (5)
-- statement:
--   The $\mathrm{MSO}_1$ formula
--   $$\mathsf{CertSP}_M(P,s,t):=\mathsf{Path}(P,s,t)\wedge\exists C_0\cdots\exists C_{M-1}\bigl(\mathsf{Part}_M(\bar C)\wedge\mathsf{Adm}_M(\bar C)\wedge\mathsf{Orient}_M(P,s,t,\bar C)\bigr).$$
--   $\mathsf{Path}$ says that $P$ is an $s$-$t$ path set. $\mathsf{Part}_M$ says that every vertex lies in exactly one $C_i$. $\mathsf{Adm}_M$ says that every neighbour of a vertex in $C_i$ lies in $C_{i-1}\cup C_i\cup C_{i+1}$. $\mathsf{Orient}_M$ says that every vertex of $P$ other than $t$ has a neighbour in $P$ with the next cyclic label.
--
--   **Formalization Note** The formula is written for a context of `dV` vertex and `dS` vertex-set variables; its bound variables are the fresh levels `dV, dV + 1, …` and `dS, dS + 1, …`, which are the page's fresh names. All building blocks are written out as on p.23.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §3.3, eq. (5), p.23 (PDF 25)

import Mathlib
import Definitions.Def_MetricMSO_Formula

namespace MetricMSO

/-- A **formula builder**: given the numbers `(dV, dS)` of vertex and vertex-set variables already in
scope, it returns a formula. Quantifier builders hand the level of the new variable (`dV`, resp.
`dS`) to their body and raise the corresponding count, so variables can be referred to by the
levels captured when they were bound. -/
abbrev Builder := ℕ × ℕ → Formula

namespace Builder

/-- A fixed formula. -/
def atom (φ : Formula) : Builder := fun _ => φ
/-- `x ∈ X`. -/
def memV (x X : ℕ) : Builder := atom (.memV x X)
/-- `E(x, y)`. -/
def adj (x y : ℕ) : Builder := atom (.adj x y)
/-- `x = y`. -/
def eqV (x y : ℕ) : Builder := atom (.eqV x y)
/-- `¬φ`. -/
def neg (b : Builder) : Builder := fun d => .neg (b d)
/-- `φ ∧ ψ`. -/
def and (a b : Builder) : Builder := fun d => .and (a d) (b d)
/-- `φ ∨ ψ`. -/
def or (a b : Builder) : Builder := fun d => Formula.or (a d) (b d)
/-- `φ → ψ`. -/
def imp (a b : Builder) : Builder := fun d => Formula.imp (a d) (b d)
/-- `∃x φ(x)`; the body receives the level of `x`. -/
def exV (k : ℕ → Builder) : Builder := fun d => .exV (k d.1 (d.1 + 1, d.2))
/-- `∀x φ(x)`. -/
def allV (k : ℕ → Builder) : Builder := neg (exV fun x => neg (k x))
/-- `∃X φ(X)`; the body receives the level of `X`. -/
def exVS (k : ℕ → Builder) : Builder := fun d => .exVS (k d.2 (d.1, d.2 + 1))
/-- `∀X φ(X)`. -/
def allVS (k : ℕ → Builder) : Builder := neg (exVS fun X => neg (k X))
/-- Finite disjunction (the empty one is `⊥`). -/
def bigOr : List Builder → Builder
  | [] => atom .ff
  | b :: bs => or b (bigOr bs)
/-- Finite conjunction (the empty one is `⊤`). -/
def bigAnd : List Builder → Builder
  | [] => atom Formula.tt
  | b :: bs => and b (bigAnd bs)
/-- `∃X₀ ∃X₁ ⋯ ∃X_{m−1} φ(X₀, …, X_{m−1})`, `X₀` outermost; the body receives the map `i ↦` level of
`X_i` (for `i < m`). -/
def exVSn : (m : ℕ) → ((ℕ → ℕ) → Builder) → Builder
  | 0, k => k fun _ => 0
  | m + 1, k => exVS fun X => exVSn m fun Xs => k fun i => if i = 0 then X else Xs (i - 1)

/-- `Y ⊆ P`. -/
def subset (Y P : ℕ) : Builder := allV fun x => imp (memV x Y) (memV x P)

/-- `G[P]` is connected (for nonempty `P`): every nonempty proper subset `Y` of `P` has an edge to
`P \ Y`. -/
def conn (P : ℕ) : Builder :=
  allVS fun Y => imp
    (and (subset Y P) (and (exV fun x => memV x Y) (exV fun x => and (memV x P) (neg (memV x Y)))))
    (exV fun x => exV fun y =>
      and (memV x Y) (and (memV y P) (and (neg (memV y Y)) (adj x y))))

/-- `x` has exactly one neighbour in `P`. -/
def deg1 (x P : ℕ) : Builder :=
  exV fun y => and (memV y P) (and (adj x y)
    (allV fun z => imp (and (memV z P) (adj x z)) (eqV z y)))

/-- `x` has exactly two neighbours in `P`. -/
def deg2 (x P : ℕ) : Builder :=
  exV fun y => exV fun z => and (neg (eqV y z)) (and (memV y P) (and (memV z P) (and (adj x y)
    (and (adj x z) (allV fun w => imp (and (memV w P) (adj x w)) (or (eqV w y) (eqV w z)))))))

/-- **Path(P, s, t)** (§3.3, p.23 (PDF 25)): "If s = t, we require P = {s}. Otherwise, we require that
s, t ∈ P, that G[P] is connected, and that s and t have degree one while every other vertex has
degree two (in the graph G[P])." -/
def path (P s t : ℕ) : Builder :=
  or (and (eqV s t) (allV fun x => and (imp (memV x P) (eqV x s)) (imp (eqV x s) (memV x P))))
    (and (neg (eqV s t)) (and (memV s P) (and (memV t P) (and (conn P)
      (allV fun x => imp (memV x P)
        (and (imp (or (eqV x s) (eqV x t)) (deg1 x P))
          (imp (and (neg (eqV x s)) (neg (eqV x t))) (deg2 x P))))))))

/-- **Part_M(C̄)**: every vertex belongs to exactly one of the sets `C_0, …, C_{M−1}`. -/
def part (M : ℕ) (C : ℕ → ℕ) : Builder :=
  allV fun x => and (bigOr (List.ofFn fun i : Fin M => memV x (C i)))
    (bigAnd (List.ofFn fun i : Fin M => bigAnd (List.ofFn fun j : Fin M =>
      if i < j then neg (and (memV x (C i)) (memV x (C j))) else atom Formula.tt)))

/-- **Adm_M(C̄)**: for each `i`, every neighbour of a vertex in `C_i` belongs to `C_{i−1}`, `C_i` or
`C_{i+1}` (indices modulo `M`). -/
def adm (M : ℕ) (C : ℕ → ℕ) : Builder :=
  bigAnd (List.ofFn fun i : Fin M => allV fun x => allV fun y =>
    imp (and (memV x (C i)) (adj x y))
      (or (memV y (C ((i + M - 1) % M))) (or (memV y (C i)) (memV y (C ((i + 1) % M))))))

/-- **Orient_M(P, s, t, C̄)** (§3.3, p.23 (PDF 25)):
`∀x ((x ∈ P ∧ x ≠ t) → ∃y (y ∈ P ∧ E(x, y) ∧ ⋁_{i=0}^{M−1} (x ∈ C_i ∧ y ∈ C_{i+1})))`. -/
def orient (M : ℕ) (P t : ℕ) (C : ℕ → ℕ) : Builder :=
  allV fun x => imp (and (memV x P) (neg (eqV x t)))
    (exV fun y => and (memV y P) (and (adj x y)
      (bigOr (List.ofFn fun i : Fin M => and (memV x (C i)) (memV y (C ((i + 1) % M)))))))

/-- **CertSP_M(P, s, t)**, eq. (5), p.23 (PDF 25):
`Path(P, s, t) ∧ ∃C_0 ⋯ ∃C_{M−1} (Part_M(C̄) ∧ Adm_M(C̄) ∧ Orient_M(P, s, t, C̄))`. -/
def certSP (M : ℕ) (P s t : ℕ) : Builder :=
  and (path P s t) (exVSn M fun C => and (part M C) (and (adm M C) (orient M P t C)))

end Builder

/-- **The shortest-path certificate `CertSP_M(P, s, t)`**, eq. (5).

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §3.3, p.23 (PDF 25):
"We describe the labeling by vertex-set variables C̄ = (C0, . . . , CM−1), where Ci contains the
vertices with label i. We read all indices modulo M … We then define CertSPM(P, s, t) :=
Path(P, s, t) ∧ ∃C0 · · · ∃CM−1 (PartM(C̄) ∧ AdmM(C̄) ∧ OrientM(P, s, t, C̄))."

`certSP M P s t dV dS` is this MSO1 formula, written for a context with `dV` vertex variables and `dS`
vertex-set variables, where `P` is the level of the set variable and `s`, `t` those of the vertex
variables; its own quantified variables get the levels `dV, dV + 1, …` and `dS, dS + 1, …`.
`Path`, `Part_M`, `Adm_M`, `Orient_M` are written out as on p.23 (see `Builder.path`,
`Builder.part`, `Builder.adm`, `Builder.orient`).

**Formalization Note** The page's fresh bound variable names are the fresh de Bruijn levels. The
canonical formula `CertSP_M(P, x, y)` of Theorem 1.5 is `certSP M 0 0 1 2 1` (`P` the set variable
of level 0, `x`, `y` the vertex variables of levels 0, 1). -/
def certSP (M : ℕ) (P s t : ℕ) (dV dS : ℕ) : Formula :=
  Builder.certSP M P s t (dV, dS)

end MetricMSO


