-- Prove2me | Definitions.Def_LinSSWorst_Supplement_IsUpslice
-- name    : LinSSWorst_Supplement_IsUpslice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:44:51.71535+00:00
-- url     : https://prove2.me/theorems/f12d4747-8ee2-41ae-80cd-a0a358d06a01
-- title:
--   Hamming weight, minterms, $(a,n)$-upslices (Definition A.8) and partitioned upslices with profile $(k-t,t)$
-- statement:
--   For $x\in\{0,1\}^n$ let $\mathrm{wt}(x)$ be its Hamming weight. A **minterm** of a monotone $F$ is an $x$ with $F(x)=1$ and $F(y)=0$ for every $y<x$.
--
--   The **$a$-upslice** of $f$ is
--   $$F(x)=\begin{cases}0 & \mathrm{wt}(x)<a,\\ f(x) & \mathrm{wt}(x)=a,\\ 1 \iff \exists x':\ \mathrm{wt}(x')=a,\ x'\le x,\ f(x')=1 & \mathrm{wt}(x)>a.\end{cases}$$
--   $F$ is an **$(a,n)$-upslice** if it is the $a$-upslice of some $n$-party access structure.
--
--   For a partition $[n]=L\sqcup R$, a **partitioned upslice $f_\Pi$ with profile $(k-t,t)$** is a $k$-upslice every minterm $M$ of which satisfies $|M\cap L|=k-t$ and $|M\cap R|=t$.
--
--   Upslices are the building blocks of the upper bounds of §§4–6.
--
--   **Formalization Note** $R$ is the complement `Lᶜ`; a minterm is identified with its set of parties. The upslice is defined by the printed case formula (Definition A.8), not by the minterm characterization the page observes.
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Definition A.8, p.31; partitioned upslices, §4, pp.13–14

import Mathlib
import Definitions.Def_LinSSWorst_Realizes

namespace LinSSWorst.Supplement

/-- The **Hamming weight** `wt(x)` of `x ∈ {0,1}ⁿ`: the number of parties of the coalition `I_x`.
From O. Nir, *Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027
submission, version of 2026-11-02, sha256 5521cfdb…), §2.1 and App. A.2, pp.30–31. -/
def wt {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun j => x j = true)).card

/-- A **minterm** of a monotone function `F`: an `x` with `F(x) = 1` such that `F(y) = 0` for every
`y < x` (a minimal authorized coalition). -/
def IsMinterm {n : ℕ} (F : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Prop :=
  F x = true ∧ ∀ y, y < x → F y = false

open scoped Classical in
/-- The **`a`-upslice** of `f` (Definition A.8, p.31):
`F(x) = 0` if `wt(x) < a`; `F(x) = f(x)` if `wt(x) = a`; and, if `wt(x) > a`, `F(x) = 1` iff there is
`x'` with `wt(x') = a`, `x' ≤ x` and `f(x') = 1`. -/
noncomputable def upslice {n : ℕ} (f : (Fin n → Bool) → Bool) (a : ℕ) (x : Fin n → Bool) : Bool :=
  if wt x < a then false
  else if wt x = a then f x
  else decide (∃ x' : Fin n → Bool, wt x' = a ∧ x' ≤ x ∧ f x' = true)

/-- `F` is an **`(a, n)`-upslice** (Definition A.8, p.31) if `F` is the `a`-upslice of some `n`-party
access structure `f`.

**Formalization Note.** Definition A.8 takes `a ∈ [n]`; the theorems using it state `1 ≤ a ≤ n`.
The page observes that `F` is an `(a, n)`-upslice iff all its minterms have weight `a`; the definition
here is the printed one. The all-false function is an `(a, n)`-upslice (the upslice of `f ≡ 0`). -/
def IsUpslice {n : ℕ} (F : (Fin n → Bool) → Bool) (a : ℕ) : Prop :=
  ∃ f : (Fin n → Bool) → Bool, IsAccessStructure f ∧ F = upslice f a

/-- A **partitioned upslice `f_Π` with profile `(k − t, t)`** (§4, pp.13–14), for the partition
`Π : [n] = L ⊔ R` with `R = [n] \ L`: a `k`-upslice in which every minterm `M` satisfies
`|M ∩ L| = k − t` and `|M ∩ R| = t`.

**Formalization Note.** `L` is a `Finset (Fin n)` and `R` is its complement `Lᶜ`; a minterm `M ∈ {0,1}ⁿ`
is identified with the set `{j | M j = true}`. "`k`-upslice" is `IsUpslice fP k`; `fP` stands for `f_Π` (an upslice of some
access structure). `k − t` is natural-number subtraction; §4 assumes `t ≤ k`. -/
def IsPartitionedUpslice {n : ℕ} (fP : (Fin n → Bool) → Bool) (L : Finset (Fin n)) (k t : ℕ) :
    Prop :=
  IsUpslice fP k ∧
    ∀ M : Fin n → Bool, IsMinterm fP M →
      (Finset.univ.filter (fun j => M j = true) ∩ L).card = k - t ∧
      (Finset.univ.filter (fun j => M j = true) ∩ Lᶜ).card = t

end LinSSWorst.Supplement


