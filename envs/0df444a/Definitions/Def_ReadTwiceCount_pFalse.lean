-- Prove2me | Definitions.Def_ReadTwiceCount_pFalse
-- name    : ReadTwiceCount_pFalse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:39.460202+00:00
-- url     : https://prove2.me/theorems/3709b2a4-d51b-4246-9ee6-54c56460c546
-- title:
--   Pinning, dangling queries, the marginal $p(H,h)$ and the coordinate $y(H,h)$
-- statement:
--   These are the notions of states and queries of §2.
--
--   1. **Pinning** a literal $l$ false substitutes it: every clause containing the complement of $l$ is deleted (it is satisfied), and every occurrence of $l$ is deleted from the other clauses. Pinning $l$ true is pinning its complement false. The universe is unchanged; the pinned variable no longer occurs.
--   2. A **dangling query** of a state $H$ is a literal $h$ whose variable occurs at most once in $H$, and if it occurs, $h$ is that occurrence. A free variable may be queried with either sign.
--   3. For a satisfiable state $H$, the **marginal** is
--   $$p(H,h)=\Pr_{\sigma\text{ uniform in }\mathrm{Sat}(H)}[h(\sigma)=0],$$
--   the probability that the literal $h$ is false under a uniformly random satisfying assignment.
--   4. For positive marginals, the **coordinate** is $y(H,h)=\dfrac{1}{p(H,h)}-1$.
--   5. A query is **positive** if $H$ is satisfiable and $p(H,h)>0$.
--
--   **Formalization Note** A state keeps the original universe, with pinned variables free; this doubles counts and changes no probability. $p$ is a rational number; for an unsatisfiable $H$, Lean's convention $x/0=0$ gives $p=0$, and every statement using $p$ assumes $Z(H)>0$.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §2, pp.2–3, displays (2), (3)

import Mathlib
import Definitions.Def_ReadTwiceCount_Formula

namespace ReadTwiceCount

variable {M : ℕ}

namespace Formula

/-- **Pinning a literal false** (He, *A Deterministic Approximation Scheme for Counting Read-Twice
CNF Assignments*, STOC 2027 submission, manuscript sha256 7a2a9dcd…, §2, p.2: "Pinning means
substitution: delete a satisfied clause and delete a falsified literal from an unsatisfied clause").
Setting the literal `l` false deletes every clause that contains its complement and deletes every
occurrence of `l` from the remaining clauses.

**Formalization Note** The state keeps the universe `Fin M`; the pinned variable no longer occurs and
is free. This doubles every count and changes no probability (`p` and `y` below are ratios). -/
def pinFalse (H : Formula M) (l : Lit M) : Formula M :=
  ⟨(H.clauses.filter fun C => decide ((l.1, !l.2) ∉ C)).map fun C => C.filter fun x => x ≠ l⟩

/-- Pinning a literal `l` true, i.e. pinning its complement false. -/
def pinTrue (H : Formula M) (l : Lit M) : Formula M := H.pinFalse (l.1, !l.2)

end Formula

/-- **A dangling query** (He, STOC 2027 submission, manuscript sha256 7a2a9dcd…, §2, p.3: "A dangling
query is a literal h whose variable occurs at most once in the state. If the variable occurs, we
choose h to be that remaining occurrence"). A free variable may be queried with either sign. -/
def IsDangling (H : Formula M) (h : Lit M) : Prop :=
  H.occ h.1 ≤ 1 ∧ (H.occ h.1 = 1 → ∃ C ∈ H.clauses, h ∈ C)

/-- The number of satisfying assignments of `H` under which the literal `h` is false. -/
def falseCount (H : Formula M) (h : Lit M) : ℕ :=
  (Finset.univ.filter fun σ : Fin M → Bool => H.eval σ = true ∧ σ h.1 ≠ h.2).card

/-- **The marginal `p(H, h)`**, display (2) (He, STOC 2027 submission, manuscript sha256 7a2a9dcd…,
§2, p.3): `p(H, h) = Pr_{σ uniform in Sat(H)}[h(σ) = 0]`, the probability that `h` is false under a
uniformly random satisfying assignment.

**Formalization Note** `h(σ) = 0` means the literal `h = (v, b)` is false, `σ v ≠ b`. The paper
defines `p` for satisfiable `H`; Lean's `x / 0 = 0` gives `0` otherwise, and every statement using `p`
assumes `Z H > 0`. -/
def pFalse (H : Formula M) (h : Lit M) : ℚ := (falseCount H h : ℚ) / (Z H : ℚ)

/-- **The coordinate `y(H, h) = 1/p(H, h) − 1`**, display (3) (He, STOC 2027 submission, manuscript
sha256 7a2a9dcd…, §2, p.3), used for positive marginals. -/
def yCoord (H : Formula M) (h : Lit M) : ℚ := 1 / pFalse H h - 1

/-- **A positive query**: `H` is satisfiable and `p(H, h) > 0` (He, STOC 2027 submission, manuscript
sha256 7a2a9dcd…, §2, p.3, "For positive marginals"). -/
def IsPositive (H : Formula M) (h : Lit M) : Prop := 0 < Z H ∧ 0 < pFalse H h

end ReadTwiceCount


