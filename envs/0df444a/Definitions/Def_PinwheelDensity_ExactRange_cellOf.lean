-- Prove2me | Definitions.Def_PinwheelDensity_ExactRange_cellOf
-- name    : PinwheelDensity_ExactRange_cellOf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:01.052828+00:00
-- url     : https://prove2.me/theorems/c80fe10f-92a3-40e5-b053-13af36909418
-- title:
--   Folding, cells, root boxes, weights and the case generators
-- statement:
--   **Kawamura's fold** $F_\theta$ acts on a decreasing list: if it is empty or its head is at most $\theta$, return it; otherwise delete the head; if nothing remains return $(\theta)$; if the new head $y$ is at most $\theta$ return $(\theta,y,\dots)$; otherwise replace $y$ by $y/2$, re-insert it in order, and recurse.
--
--   For an even level $\theta=2h\ge4$ and an integer list $A$, the **fold** is $b=\mathrm{sort}\,F_\theta(A^\downarrow)$ in increasing order. With $R_\theta(x)=x$ for $x\le h$ and $R_\theta(x)=\lceil x\rceil-1$ for $x>h$, the **cell** is $c=R_\theta(b)$ coordinatewise. Its **root box** is $\ell_i=c_i$, with $u_i=c_i$ if $c_i<h$ and $u_i=c_i+1$ otherwise. Its **weight** is
--   $$\mathrm{wt}_\theta(c)=\sum_{c_i<h}\frac1{c_i}+\sum_{c_i\ge h}\frac1{c_i+1}.$$
--   A **target** has all entries at least $m$ and density at most $B$, and $\beta_\theta=B+1/\theta$. A **box member** $b$ satisfies $\ell\le b\le u$ componentwise with equal lengths, $b>0$ and the strict inequality $D(b)<\beta$.
--
--   The **initial case set** $K_{\theta_0}$ consists of the nonempty nondecreasing integer lists with entries in $[\min(m,h_0),\theta_0)$ and weight below $\beta_{\theta_0}$, and the checker enumerates it by extending sorted prefixes under this strict filter with fuel $\lceil\theta_0B\rceil+1$. The **unfolding generator** $U_\theta^B(c)$ lists all sorted lists
--   $$c_0+[h]^{n_h-g-p}+[h+1]^p+[\theta-1]^{n_{\theta-1}-o}+[\theta]^{2g+o-v}+[\theta+1]^v$$
--   over $g+p\le n_h$, $o\in\{0,1\}$, $o\le n_{\theta-1}$, $v\le 2g+o$ that pass the weight filter at $\theta+2$. Exponents are multiplicities.
--
--   These objects reduce the infinite family of targets to finitely many cases at each level.
--
--   **Formalization Note** The cell is natural-valued, with $\lfloor x\rfloor$ on the low branch, as in the source's Lean; the two agree on the integers that occur. The enumeration of $K_{12}$ evaluates to the source's 6,403 and 5,540 elements for $(m,B)=(4,17/20)$ and $(5,13/15)$.
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Appendix A, p. 11; Appendix B, pp. 11–13; Appendix C, p. 14 (same PDF pages)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable

namespace PinwheelDensity.ExactRange

/-- Kawamura's fold `F_θ` on a list sorted decreasingly (Appendix A, p. 11): stop if the list is
empty or its head is at most `θ`; otherwise delete the head; if nothing remains return `(θ)`; if the
new head `y` is at most `θ` return `(θ, y, …)`; otherwise replace `y` by `y/2`, re-insert it in
decreasing order and recurse. The length drops at each recursive call. -/
def foldDown (θ : ℚ) : List ℚ → List ℚ
  | [] => []
  | x :: l =>
    if x ≤ θ then x :: l
    else
      match l with
      | [] => [θ]
      | y :: l' =>
        if y ≤ θ then θ :: y :: l'
        else foldDown θ (List.orderedInsert (· ≥ ·) (y / 2) l')
termination_by l => l.length
decreasing_by
  simp [List.orderedInsert_length]

/-- Increasing sort of a rational list. -/
def sortQ (l : List ℚ) : List ℚ :=
  l.insertionSort (· ≤ ·)

/-- The fold `b = sort F_θ(A↓)` of an integer list at level `θ` (Appendix B, p. 11). -/
def foldOf (θ : ℕ) (A : List ℕ) : List ℚ :=
  sortQ (foldDown (θ : ℚ) ((toQ A).insertionSort (· ≥ ·)))

/-- The rounding `R_θ`, `θ = 2h` (Appendix B, p. 11): `x` for `x ≤ h` and `⌈x⌉ - 1` for `x > h`.
Natural-valued; the low branch uses `⌊x⌋`, as the source's own Lean does, which agrees with `x` on
the integers that occur there. -/
def roundCell (θ : ℕ) (x : ℚ) : ℕ :=
  if x ≤ ((θ / 2 : ℕ) : ℚ) then ⌊x⌋₊ else ⌈x⌉₊ - 1

/-- The cell `c = R_θ(b)`, coordinatewise (Appendix B, p. 12). -/
def cellOf (θ : ℕ) (A : List ℕ) : List ℕ :=
  (foldOf θ A).map (roundCell θ)

/-- Lower root bounds `ℓᵢ = cᵢ` (Appendix B, p. 12). -/
def rootLo (c : List ℕ) : List ℚ :=
  toQ c

/-- Upper root bounds: `uᵢ = cᵢ` if `cᵢ < h`, otherwise `uᵢ = cᵢ + 1` (Appendix B, p. 12). -/
def rootUp (θ : ℕ) (c : List ℕ) : List ℚ :=
  c.map fun x => if x < θ / 2 then (x : ℚ) else (x : ℚ) + 1

/-- `wt_θ(c) = ∑_{cᵢ < h} 1/cᵢ + ∑_{cᵢ ≥ h} 1/(cᵢ + 1)` (Appendix B, p. 12). -/
def weight (θ : ℕ) (c : List ℕ) : ℚ :=
  (c.map fun x => if x < θ / 2 then (1 : ℚ) / (x : ℚ) else (1 : ℚ) / ((x : ℚ) + 1)).sum

/-- `β_θ = B + 1/θ` (Appendix B, p. 11). -/
def beta (B : ℚ) (θ : ℕ) : ℚ :=
  B + 1 / (θ : ℚ)

/-- A target (Appendix B, p. 11): all entries at least `m`, density at most `B` (non-strict). -/
def IsTarget (m : ℕ) (B : ℚ) (A : List ℕ) : Prop :=
  (∀ a ∈ A, m ≤ a) ∧ density A ≤ B

/-- Componentwise `≤`; `false` on lists of different lengths. -/
def leAll : List ℚ → List ℚ → Bool
  | [], [] => true
  | a :: l, b :: m => decide (a ≤ b) && leAll l m
  | _, _ => false

/-- Box membership (Appendix C, p. 14): `ℓ ≤ b ≤ u` componentwise with matching lengths, `b > 0`
and the strict inequality `D(b) < β`. -/
def IsBoxMember (ℓ u : List ℚ) (β : ℚ) (b : List ℚ) : Prop :=
  leAll ℓ b = true ∧ leAll b u = true ∧ (∀ x ∈ b, 0 < x) ∧ densityQ b < β

/-- Generic enumerator of nondecreasing lists with entries in `[lo, hi)` (Appendix B, p. 12): it
extends the prefix `pref` by each admissible value and keeps an extension (and continues from it)
only if `ok` accepts it. The fuel bounds the number of added entries. The empty list is not output. -/
def enumSorted (ok : List ℕ → Bool) (lo hi : ℕ) : ℕ → List ℕ → List (List ℕ)
  | 0, _ => []
  | fuel + 1, pref =>
    let start := max lo (pref.getLast?.getD lo)
    (List.range' start (hi - start)).flatMap fun v =>
      let p := pref ++ [v]
      if ok p then p :: enumSorted ok lo hi fuel p else []

/-- The set `K_θ₀` (Appendix B, p. 12): nonempty nondecreasing lists with entries in
`[min(m, h₀), θ₀)` and weight strictly below `β_θ₀`. -/
def InitialCases (m : ℕ) (B : ℚ) (θ₀ : ℕ) : Set (List ℕ) :=
  {c | c ≠ [] ∧ c.Pairwise (· ≤ ·) ∧ (∀ x ∈ c, min m (θ₀ / 2) ≤ x ∧ x < θ₀) ∧
    weight θ₀ c < beta B θ₀}

/-- The checker's enumeration of `K_θ₀`: the strict weight filter, with fuel `⌈θ₀ B⌉ + 1`
(Appendix B, p. 12). -/
def initCases (m : ℕ) (B : ℚ) (θ₀ : ℕ) : List (List ℕ) :=
  enumSorted (fun p => decide (weight θ₀ p < beta B θ₀)) (min m (θ₀ / 2)) θ₀
    (⌈(θ₀ : ℚ) * B⌉₊ + 1) []

/-- The multiset form of Proposition B.5, p. 13, as a list:
`c₀ + [h]^(n_h-g-p) + [h+1]^p + [θ-1]^(n_{θ-1}-o) + [θ]^(2g+o-v) + [θ+1]^v`, where `c₀` holds the
entries of `c` different from `h` and `θ - 1`. Exponents are multiplicities. -/
def unfoldForm (θ : ℕ) (c : List ℕ) (g p o v : ℕ) : List ℕ :=
  c.filter (fun x => x ≠ θ / 2 ∧ x ≠ θ - 1) ++
    List.replicate (c.count (θ / 2) - g - p) (θ / 2) ++
    List.replicate p (θ / 2 + 1) ++
    List.replicate (c.count (θ - 1) - o) (θ - 1) ++
    List.replicate (2 * g + o - v) θ ++
    List.replicate v (θ + 1)

/-- The admissible parameters of Proposition B.5, p. 13: `g + p ≤ n_h`, `o ∈ {0, 1}`,
`o ≤ n_{θ-1}`, `v ≤ 2g + o`. -/
def UnfoldAdmissible (θ : ℕ) (c : List ℕ) (g p o v : ℕ) : Prop :=
  g + p ≤ c.count (θ / 2) ∧ o ≤ 1 ∧ o ≤ c.count (θ - 1) ∧ v ≤ 2 * g + o

/-- The generator `U_θ^B(c)` (Proposition B.5, p. 13): every sorted list of the form `unfoldForm`
over admissible `(g, p, o, v)` passing the strict weight filter at stage `θ + 2`. -/
def unfoldCell (B : ℚ) (θ : ℕ) (c : List ℕ) : List (List ℕ) :=
  (List.range (c.count (θ / 2) + 1)).flatMap fun g =>
    (List.range (c.count (θ / 2) - g + 1)).flatMap fun p =>
      (List.range (min 1 (c.count (θ - 1)) + 1)).flatMap fun o =>
        (List.range (2 * g + o + 1)).filterMap fun v =>
          let d := (unfoldForm θ c g p o v).insertionSort (· ≤ ·)
          if weight (θ + 2) d < beta B (θ + 2) then some d else none

end PinwheelDensity.ExactRange


