-- Prove2me | Definitions.Def_MatchIndiff_PublicSM_Model
-- name    : MatchIndiff_PublicSM_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:24:52.849553+00:00
-- url     : https://prove2.me/theorems/2c4fbea8-cae8-4f9c-a6cd-eadfa79f570c
-- title:
--   School choice with ties: weak rows, matchings with ⊥, weak/strong/super stability, the canonical selectors Φ_s, Φ_u with †, rank and exact outputs (§2, App. C.1.2, §D.7–D.8)
-- statement:
--   One-to-one school choice with $n$ students $N$ and $m$ schools $H$ (unit capacities).
--
--   **Rows.** A student's report is a *weak row* $P_i=(C_i^1,\dots,C_i^{\ell_i})$: an ordered list of nonempty, pairwise disjoint tie classes of acceptable schools; omitted schools are unacceptable and the empty row is allowed. A public school priority $Q_h$ is a weak row over students (ties and unacceptable students allowed). The tie-class index of an acceptable partner $a$ is $\mathrm{rk}_i(a;P_i)$; the outside option $\bot$ (unmatched) has rank $m+1$ for a student and $n+1$ for a school. Every acceptable partner is strictly better than $\bot$ and $\bot$ is strictly better than every unacceptable partner.
--
--   **Matchings.** A matching $\mu$ gives each student a school or $\bot$, with no school receiving two students; $\mu(h)$ is the student at $h$ or $\bot$. It is *individually rational* if every matched pair is mutually acceptable.
--
--   **Blocking and stability (p. 7).** A pair $(d,h)$ not in $\mu$ *weakly blocks* if both $d$ and $h$ strictly prefer each other to their current partners; it *strongly blocks* if both weakly prefer each other and at least one comparison is strict; it *super-blocks* if both comparisons are weak. A matching is weakly / strongly / super stable if it is individually rational and has no pair of the corresponding kind.
--
--   **Public input and canonical selectors (p. 7; C.1.2, p. 68).** The public input $\xi=(Q,\rho,\tau)$ consists of the school priorities, a public student order $d_1,\dots,d_n$ and a public school order (school $h$ has identifier $\tau(h)$, $\bot$ has identifier $m+1$). For a profile $P$,
--   $$\mathrm{key}(\mu;P)=\big(\mathrm{rk}_{d_1}(\mu(d_1)),\dots,\mathrm{rk}_{d_n}(\mu(d_n)),\ \mathrm{id}(\mu(d_1)),\dots,\mathrm{id}(\mu(d_n))\big),$$
--   compared lexicographically. For $\alpha\in\{s,u\}$ the selector $\Phi_\alpha(P)$ is the strongly ($s$) or super ($u$) stable matching with minimum key, and the failure symbol $\dagger$ when no such matching exists.
--
--   **Outputs (p. 6).** The exact output of student $i$ is $\Phi^E_i(P)=\Phi_\alpha(P)(i)$ (a school or $\bot$); the rank output is $\Phi^I_i(P)=\mathrm{rk}_i(\Phi_\alpha(P)(i);P_i)$, the tie-class rank in the student's own row ($m+1$ for $\bot$). Both are $\dagger$ when $\Phi_\alpha(P)=\dagger$.
--
--   The file also defines $m_Q=|\{(d,h): d \text{ acceptable to } h\}|$; an *improvement* of $\mu$ (§D.8.3, p. 102): an $\alpha$-stable matching with at least one change in which every changed student strictly improves and every changed school strictly worsens; and the *tie graph* of $\mu$ (§D.7, p. 97): matched student $d$ and matched school $h$ are adjacent exactly when $h\sim_d\mu(d)$ and $d\sim_h\mu(h)$.
--
--   **Formalization Note.** Students are `Fin n`, schools `Fin m`. A row is a function `r : Fin k → ℕ` with `r a = 0` for unacceptable and `r a = j ≥ 1` for the $j$-th tie class, gap-free (`IsRow`: every used class $j\ge 2$ has class $j-1$ used), so tie-class indices are canonical. `rk r : Option (Fin k) → ℕ` gives `none` ($\bot$) the value $k+1$ and an unacceptable partner $k+2$. A matching stores each student's `Option` school with unit capacity; `holder` recovers $\mu(h)$. The public student order is `ρ : Fin n ≃ Fin n` (student $i$ is $d_{\rho(i)+1}$), the school order `τ : Fin m ≃ Fin m` (identifier $\tau(h)+1$). `select α ξ P : Option (Matching n m)` is `none` for $\dagger$; `Out m .rank = Option ℕ`, `Out m .exact = Option (Option (Fin m))` with `none` the failure symbol.
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), pp. 5–7 (§2: rows, ranks, matchings, stable selectors, rank and exact outputs); p. 68 (C.1.2, key(µ; P)); p. 97 (tie graph); pp. 99, 102 (m_Q, improvement)

import Mathlib

namespace MatchIndiff.PublicSM

/-- A weak preference row over a finite set of partners `α`, encoded by tie-class index:
`r a = 0` means `a` is unacceptable, and `r a = k ≥ 1` means `a` lies in the `k`-th acceptable
tie class (1-based, smaller is better). The row is gap-free: whenever tie class `k ≥ 2` is
used, tie class `k - 1` is used too, so the acceptable values are exactly `{1, …, ℓ}` and
tie-class indices are canonical. The empty row (all zero) is allowed. Zhang–Zhao–Xu–Xi–Zhao, p. 5. -/
def IsRow {α : Type*} (r : α → ℕ) : Prop :=
  ∀ a, 2 ≤ r a → ∃ b, r b + 1 = r a

/-- The rank of an optional partner in a row over `Fin k`: an acceptable partner gets its
tie-class index, the outside option `⊥` (`none`) gets `k + 1` (the paper's `m + 1` for a student,
`n + 1` for a school), and an unacceptable partner gets `k + 2`, strictly below `⊥`. Smaller is
better. -/
def rk {k : ℕ} (r : Fin k → ℕ) : Option (Fin k) → ℕ
  | none => k + 1
  | some a => if r a = 0 then k + 2 else r a

/-- A one-to-one (unit-capacity) matching of `n` students and `m` schools: each student gets a
school or `⊥` (`none`), and no school receives two students. -/
@[ext]
structure Matching (n m : ℕ) where
  /-- the school of each student, `none` for unmatched -/
  toFun : Fin n → Option (Fin m)
  /-- unit capacity -/
  inj : ∀ (i j : Fin n) (h : Fin m), toFun i = some h → toFun j = some h → i = j

/-- The student held by school `h` under `μ`, or `none` (`⊥`) when `h` is unmatched. -/
def Matching.holder {n m : ℕ} (μ : Matching n m) (h : Fin m) : Option (Fin n) :=
  (List.finRange n).find? (fun i => μ.toFun i = some h)

/-- The three stability notions. -/
inductive StabKind
  | weak
  | strong
  | super
  deriving DecidableEq

/-- Individual rationality: every matched pair is mutually acceptable. Student rows `P i` are
over schools, public school rows `Q h` are over students. -/
def IsIR {n m : ℕ} (P : Fin n → Fin m → ℕ) (Q : Fin m → Fin n → ℕ) (μ : Matching n m) : Prop :=
  ∀ (i : Fin n) (h : Fin m), μ.toFun i = some h → P i h ≠ 0 ∧ Q h i ≠ 0

/-- The pair `(i, h)`, not in `μ`, blocks `μ` in the sense `α` (p. 7): weakly blocks when both
endpoints strictly prefer each other to their current partners; strongly blocks when both weakly
prefer each other and at least one comparison is strict; super-blocks when both comparisons are
weak. Comparisons use `rk`, so every acceptable partner beats `⊥` and `⊥` beats every
unacceptable partner. -/
def Blocks {n m : ℕ} (α : StabKind) (P : Fin n → Fin m → ℕ) (Q : Fin m → Fin n → ℕ)
    (μ : Matching n m) (i : Fin n) (h : Fin m) : Prop :=
  μ.toFun i ≠ some h ∧
    match α with
    | .weak => rk (P i) (some h) < rk (P i) (μ.toFun i) ∧ rk (Q h) (some i) < rk (Q h) (μ.holder h)
    | .strong => rk (P i) (some h) ≤ rk (P i) (μ.toFun i) ∧ rk (Q h) (some i) ≤ rk (Q h) (μ.holder h) ∧
        (rk (P i) (some h) < rk (P i) (μ.toFun i) ∨ rk (Q h) (some i) < rk (Q h) (μ.holder h))
    | .super => rk (P i) (some h) ≤ rk (P i) (μ.toFun i) ∧ rk (Q h) (some i) ≤ rk (Q h) (μ.holder h)

/-- `α`-stability: individually rational and no `α`-blocking pair. -/
def IsStable {n m : ℕ} (α : StabKind) (P : Fin n → Fin m → ℕ) (Q : Fin m → Fin n → ℕ)
    (μ : Matching n m) : Prop :=
  IsIR P Q μ ∧ ∀ (i : Fin n) (h : Fin m), ¬ Blocks α P Q μ i h

/-- The public input `ξ` of public-priority school choice with `n` students and `m` schools:
the public school rows `Q`, the public student order `ρ` (student `i` is the `(ρ i + 1)`-th
student `d_{ρ i + 1}`), and the public school order `τ` (school `h` has identifier `τ h + 1`). -/
structure PublicInput (n m : ℕ) where
  /-- public school priorities, rows over students (ties and unacceptable students allowed) -/
  Q : Fin m → Fin n → ℕ
  /-- public student order -/
  ρ : Fin n ≃ Fin n
  /-- public school order -/
  τ : Fin m ≃ Fin m

/-- An eligible public input: every public school row is a valid weak row. -/
def PublicInput.Valid {n m : ℕ} (ξ : PublicInput n m) : Prop :=
  ∀ h, IsRow (ξ.Q h)

/-- The student rank vector `(rk_{d_1}(µ(d_1)), …, rk_{d_n}(µ(d_n)))` in the public student
order `ρ`. -/
def rankVec {n m : ℕ} (ρ : Fin n ≃ Fin n) (P : Fin n → Fin m → ℕ) (μ : Matching n m) : List ℕ :=
  List.ofFn (fun k : Fin n => rk (P (ρ.symm k)) (μ.toFun (ρ.symm k)))

/-- The partner-identity vector in the public student order `ρ`: school `h` is identified by
`τ h + 1`, and `⊥` by `m + 1`. -/
def idVec {n m : ℕ} (ρ : Fin n ≃ Fin n) (τ : Fin m ≃ Fin m) (μ : Matching n m) : List ℕ :=
  List.ofFn (fun k : Fin n =>
    match μ.toFun (ρ.symm k) with
    | none => m + 1
    | some h => (τ h : ℕ) + 1)

/-- `key(µ; P)` (Appendix C.1.2, p. 68): the rank vector followed by the identity vector,
compared lexicographically. -/
def key {n m : ℕ} (ξ : PublicInput n m) (P : Fin n → Fin m → ℕ) (μ : Matching n m) : List ℕ :=
  rankVec ξ.ρ P μ ++ idVec ξ.ρ ξ.τ μ

/-- `µ` is the canonical `α`-stable matching at `(ξ, P)`: it is `α`-stable and no `α`-stable
matching has a lexicographically smaller key. -/
def IsCanonical {n m : ℕ} (α : StabKind) (ξ : PublicInput n m) (P : Fin n → Fin m → ℕ)
    (μ : Matching n m) : Prop :=
  IsStable α P ξ.Q μ ∧
    ∀ ν : Matching n m, IsStable α P ξ.Q ν → ¬ List.Lex (· < ·) (key ξ P ν) (key ξ P μ)

/-- The canonical selector `Φ_α` (p. 7 and p. 68): the `α`-stable matching with minimum key,
or `†` (`none`) when no `α`-stable matching exists. (There are finitely many matchings and the
key determines the matching, so the minimizer exists and is unique whenever the stable set is
nonempty.) -/
noncomputable def select {n m : ℕ} (α : StabKind) (ξ : PublicInput n m)
    (P : Fin n → Fin m → ℕ) : Option (Matching n m) :=
  open Classical in
  if hμ : ∃ μ, IsCanonical α ξ P μ then some (Classical.choose hμ) else none

/-- The output type: rank (`I`) or exact (`E`). -/
inductive OutKind
  | rank
  | exact
  deriving DecidableEq

/-- The local output alphabet `X^b_v` of a student: for rank output an optional natural number
(`none` is `†`), for exact output an optional partner-or-`⊥` (`none` is `†`, `some none` is
`⊥`). -/
def Out (m : ℕ) : OutKind → Type
  | .rank => Option ℕ
  | .exact => Option (Option (Fin m))

/-- The desired local output `Φ^b_i(P)` (p. 6): the exact partner (`⊥` or a school), or the
tie-class rank of that partner in the student's own row (`m + 1` for `⊥`); `†` for every student
when the selector fails. -/
noncomputable def phiOut {n m : ℕ} (α : StabKind) (ξ : PublicInput n m) (b : OutKind)
    (P : Fin n → Fin m → ℕ) (i : Fin n) : Out m b :=
  match b with
  | .rank => (select α ξ P).map (fun μ => rk (P i) (μ.toFun i))
  | .exact => (select α ξ P).map (fun μ => μ.toFun i)

/-- The number `m_Q` of public pairs `(d, h)` with `d` acceptable to `h`. -/
def mQ {n m : ℕ} (Q : Fin m → Fin n → ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin m => Q p.2 p.1 ≠ 0)).card

/-- An improvement of `µ` (§D.8.3, p. 102): an `α`-stable matching `N` with at least one change,
in which every changed student strictly improves and every changed school strictly worsens. -/
def IsImprovement {n m : ℕ} (α : StabKind) (P : Fin n → Fin m → ℕ) (Q : Fin m → Fin n → ℕ)
    (μ N : Matching n m) : Prop :=
  IsStable α P Q N ∧ (∃ d, N.toFun d ≠ μ.toFun d) ∧
    (∀ d, N.toFun d ≠ μ.toFun d → rk (P d) (N.toFun d) < rk (P d) (μ.toFun d)) ∧
    (∀ h, N.holder h ≠ μ.holder h → rk (Q h) (μ.holder h) < rk (Q h) (N.holder h))

/-- The tie graph of `µ` (§D.7, p. 97): matched student `d` and matched school `h` are adjacent
exactly when `h ∼_d µ(d)` and `d ∼_h µ(h)`. -/
def TieEdge {n m : ℕ} (P : Fin n → Fin m → ℕ) (Q : Fin m → Fin n → ℕ) (μ : Matching n m)
    (d : Fin n) (h : Fin m) : Prop :=
  (μ.toFun d).isSome ∧ (μ.holder h).isSome ∧
    rk (P d) (some h) = rk (P d) (μ.toFun d) ∧ rk (Q h) (some d) = rk (Q h) (μ.holder h)

end MatchIndiff.PublicSM


