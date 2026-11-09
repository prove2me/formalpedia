-- Prove2me | Definitions.Def_ElimAgree_disjAns
-- name    : ElimAgree_disjAns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:27:11.479201+00:00
-- url     : https://prove2.me/theorems/db0f1344-55fb-45e1-a401-a5c0ff8f8a4b
-- title:
--   $\mathrm{Elim}(\mathrm{DISJ}_n^k)$ and $R^{\mathrm{pub,com}}_\varepsilon$
-- statement:
--   Each party holds $k$ subsets of $[n]$: Alice holds $X=(x_1,\dots,x_k)$ and Bob holds $Y=(y_1,\dots,y_k)$. With $\mathrm{DISJ}_n(x,y)=1$ when $x\cap y=\emptyset$ and $0$ otherwise, the answer vector is
--   $$F(X,Y)=\big(\mathrm{DISJ}_n(x_1,y_1),\dots,\mathrm{DISJ}_n(x_k,y_k)\big)\in\{0,1\}^k .$$
--   In $\mathrm{Elim}(\mathrm{DISJ}_n^k)$ the parties must output some $\sigma\in\{0,1\}^k$ with $\sigma\ne F(X,Y)$. The **common-output randomized complexity** $R^{\mathrm{pub,com}}_\varepsilon(\mathrm{Elim}(\mathrm{DISJ}_n^k))$ is the least cost $c$ of a public-coin common-output protocol whose failure probability is at most $\varepsilon$ on every input.
--
--   **Formalization Note** $[n]$ is `Fin n`, sets are `Finset (Fin n)`, and $\{0,1\}$ is `Bool` with $\mathrm{DISJ}=1$ as `true`. The complexity is an infimum over a set of natural numbers, which is nonempty for $k\ge1$.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), §1, p.1 (PDF p.3); Definition 2.1, p.6 (PDF p.8); §3, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_ElimAgree_ComLabel

namespace ElimAgree

/-- An input of one party to `k` instances of disjointness on `[n]`: a `k`-tuple of subsets of
`[n] = Fin n` (Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in
Elimination*, manuscript, STOC 2027 submission, §1, p.1). -/
abbrev Inp (n k : ℕ) : Type := Fin k → Finset (Fin n)

/-- The answer vector `F(X, Y) = (DISJ_n(x_1, y_1), …, DISJ_n(x_k, y_k))` (§1 and §3, pp.1, 7):
`DISJ_n(x, y) = 1` iff `x` and `y` are disjoint.

**Formalization Note.** `{0, 1}` is `Bool`, with `DISJ = 1` encoded as `true`. -/
def disjAns {n k : ℕ} (X Y : Inp n k) : Fin k → Bool :=
  fun i => decide (Disjoint (X i) (Y i))

/-- Common-output protocol trees for `Elim(DISJ_n^k)`: both parties' leaf outputs are vectors in
`{0, 1}^k`. -/
abbrev ComProt (n k : ℕ) : Type :=
  OneOfManyCC.Protocol (Inp n k) (Inp n k) (ComLabel (Inp n k) (Inp n k) (Fin k → Bool))

/-- `R^{pub,com}_ε(Elim(DISJ_n^k))` (Definition 2.1, p.6): the least worst-case cost of a
public-coin common-output protocol whose failure probability is at most `ε` on every input.

**Formalization Note.** The set is nonempty for every `k ≥ 1` (Alice sends `x_1`, Bob replies with
the complement of `DISJ(x_1, y_1)`), so the `sInf ∅ = 0` convention is never used there. -/
noncomputable def Rcom (n k : ℕ) (ε : ℝ) : ℕ :=
  sInf {c : ℕ | ∃ μ : PMF (ComProt n k), CostLE μ c ∧
    ∀ X Y : Inp n k, comErr disjAns μ X Y ≤ ENNReal.ofReal ε}

end ElimAgree


