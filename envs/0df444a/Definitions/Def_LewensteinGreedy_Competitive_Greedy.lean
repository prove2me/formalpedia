-- Prove2me | Definitions.Def_LewensteinGreedy_Competitive_Greedy
-- name    : LewensteinGreedy_Competitive_Greedy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:31:08.439864+00:00
-- url     : https://prove2.me/theorems/56ed564a-abd3-44ae-a8a7-1d1b7b9a278a
-- title:
--   Online geometric Greedy on a height profile: $C(X;h)$, $\mathrm{Greedy}(X,T_0)$, $\lambda$ and the label function $F$
-- statement:
--   A height profile assigns a real height $h(v)$ to every key; any finite real profile is allowed, ties included (§2.2.2).
--
--   **Touch rule (2.1).** For a request to $x$, Greedy touches $x$ and every $v\in[n]$, $v\neq x$, such that $h(z)<h(v)$ for every $z\in[\min\{x,v\},\max\{x,v\}]\setminus\{v\}$ (column $x$ included; equal heights block). All tests use the old profile. Only after the whole touch set is selected do all touched keys receive one common new height above every current height; other heights are unchanged.
--
--   $C(X;h)$ is the total number of touches over the requests of $X$ in order. For an initial BST $T_0$, the initial profile is $h_0(v)=-\mathrm{depth}_{T_0}(v)$ (edge depth, root $0$) and $\mathrm{Greedy}(X,T_0)=C(X;-\mathrm{depth}_{T_0})$; the initial points are not charged.
--
--   $\lambda(s)=1+\log_2\log_2(s+2)$. For $q\in\mathbb N$, $\mathrm{bitlen}(0)=0$, $\mathrm{bitlen}(q)=1+\lfloor\log_2 q\rfloor$ for $q\ge1$, and $F(q)=1+\mathrm{bitlen}(q)$.
--
--   **Formalization Note.** `Profile = ℕ → ℝ` (values off $[n]$ are never read). `touches n x h` is the rule (2.1); `greedyStep n x h` raises the touched keys to $\max_{v\in[n]}h(v)+1$; by Lemma 2.2 (only the weak order of heights matters) this gives the same touch sets as raising them to the time $t$ for a tree-encoded start. `profileAfter`, `touchRows` run the requests in order; `cost n X h` $=C(X;h)$; `initialProfile T` $=-\mathrm{depth}_T$; `greedyCost n X T` $=\mathrm{Greedy}(X,T)$; `lambda`, `bitlen`, `label` $=F$ as above. `maxHeight J h` is the maximum of $h$ on a finite set ($0$ on the empty set, never used for $n\ge1$).
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, §1.2, §2.1.3–2.2.2, eq. (2.1), §2.4 eq. (2.3), printed p. 2, 5–6, 8 / PDF 3, 6–7, 9

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn

set_option autoImplicit false

noncomputable section

namespace LewensteinGreedy.Competitive

/-!
# Online geometric Greedy on a height profile: `C(X; h)`, `Greedy(X, T₀)`, `λ`, `F`

Lewenstein, *Greedy BST is O(log log n)-Competitive*, supplied 2026 artifact (SHA-256
04ac49f6…), §1.2 printed p.2 / PDF 3; §2.1.3–2.2.2 printed pp.5–7 / PDF 6–8, equation (2.1);
§2.4 printed p.8 / PDF 9, equation (2.3).

* A height profile is `h : ℕ → ℝ`; only its values on `[n]` matter. Any finite real profile is
  allowed, ties included (§2.2.2).
* `touches n x h` is the touch set of a request to `x` under (2.1): `x` itself and every
  `v ∈ [n]`, `v ≠ x`, with `h z < h v` for **every** `z ∈ [min x v, max x v]`, `z ≠ v` (column `x`
  included). Equal heights block. All tests read the same old profile `h`.
* `greedyStep n x h`: after the whole touch set is selected, every touched key gets one common
  new height `max_{v ∈ [n]} h v + 1`, strictly above all current heights; other heights are
  unchanged. (The source uses the time `t` for a tree-encoded start and "one common value greater
  than every current height" in general; by Lemma 2.2 only the weak order matters, and both give
  the same touch sets.)
* `cost n X h = C(X; h)`: the total number of touches over the requests of `X`, in order.
* `initialProfile T₀ = −depth_{T₀}` (edge depth, root `0`), and
  `greedyCost n X T₀ = Greedy(X, T₀) = C(X; −depth_{T₀})`; the initial points are not charged.
* `lambda s = λ(s) = 1 + log₂ log₂ (s + 2)`.
* `bitlen 0 = 0`, `bitlen q = 1 + ⌊log₂ q⌋` for `q ≥ 1`, and `label q = F(q) = 1 + bitlen q`.
-/

/-- A height profile on keys. -/
abbrev Profile := ℕ → ℝ

/-- Greedy's touch set (2.1) for a request to `x`, read from the old profile `h`. -/
def touches (n x : ℕ) (h : Profile) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter fun v => v = x ∨
    ∀ z ∈ Finset.Icc (min x v) (max x v), z ≠ v → h z < h v

/-- Maximum of `h` on a finite key set (`0` on the empty set, which is never used with `n ≥ 1`). -/
def maxHeight (J : Finset ℕ) (h : Profile) : ℝ :=
  if hJ : J.Nonempty then J.sup' hJ h else 0

/-- One access: raise every touched key to one common height above all current heights. -/
def greedyStep (n x : ℕ) (h : Profile) : Profile := by
  classical
  exact fun v => if v ∈ touches n x h then maxHeight (Finset.Icc 1 n) h + 1 else h v

/-- The profile after serving the requests of `X` in order. -/
def profileAfter (n : ℕ) (X : List ℕ) (h : Profile) : Profile :=
  X.foldl (fun p x => greedyStep n x p) h

/-- The rows of touch sets, one per request. -/
def touchRows (n : ℕ) : List ℕ → Profile → List (Finset ℕ)
  | [], _ => []
  | x :: xs, h => touches n x h :: touchRows n xs (greedyStep n x h)

/-- `C(X; h)`: total number of geometric touches of Greedy on `X` from profile `h`. -/
def cost (n : ℕ) (X : List ℕ) (h : Profile) : ℕ :=
  ((touchRows n X h).map Finset.card).sum

/-- The initial profile `−depth_{T₀}` encoding an initial BST. -/
def initialProfile (T : BinaryTree ℕ) : Profile := fun v => -(SplayDynOpt.depth v T : ℝ)

/-- `Greedy(X, T₀) = C(X; −depth_{T₀})`. -/
def greedyCost (n : ℕ) (X : List ℕ) (T : BinaryTree ℕ) : ℕ := cost n X (initialProfile T)

/-- `λ(s) = 1 + log₂ log₂ (s + 2)` (§1.2). -/
def lambda (s : ℕ) : ℝ := 1 + Real.logb 2 (Real.logb 2 ((s : ℝ) + 2))

/-- `bitlen 0 = 0`, `bitlen q = 1 + ⌊log₂ q⌋` (§2.4). -/
def bitlen (q : ℕ) : ℕ := if q = 0 then 0 else 1 + Nat.log 2 q

/-- The label function `F(q) = 1 + bitlen q` of (2.3). -/
def label (q : ℕ) : ℕ := 1 + bitlen q

end LewensteinGreedy.Competitive


