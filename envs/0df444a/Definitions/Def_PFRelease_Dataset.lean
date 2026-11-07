-- Prove2me | Definitions.Def_PFRelease_Dataset
-- name    : PFRelease_Dataset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:39.792897+00:00
-- url     : https://prove2.me/theorems/f20a7645-ff44-49ac-a498-32698412fc18
-- title:
--   Datasets with null records, nulling $s^{I\to\perp}$, and $\mathcal X^*$
-- statement:
--   Augment the data domain with a **null record** $\perp$ and write $\mathcal X$ for the augmented domain. A **dataset** of $n$ slots is a sequence $s=(s_1,\dots,s_n)\in\mathcal X^n$; null records occupy their slots and count in the size $|s|=n$. For $I\subseteq[n]$ the dataset $s^{I\to\perp}$ is obtained from $s$ by replacing $s_i$ with $\perp$ for every $i\in I$, and $s^{i\to\perp}:=s^{\{i\}\to\perp}$. Every dataset of $n$ slots is also an element of $\mathcal X^*=\bigcup_{n\ge0}\mathcal X^n$, the list of its records in slot order.
--
--   Two datasets are **zero-out neighbours**, $s\simeq s'$, if they are $s$ and $s^{i\to\perp}$ for some slot $i$. All privacy notions of the mission are stated with this adjacency.
--
--   **Formalization Note** A dataset is `Fin n → Option X` (`none` is $\perp$, slots are $0,\dots,n-1$); `nullOut s I` is $s^{I\to\perp}$ and `toList s` is $s$ as a list. The type synonym `Dataset X n` carries the discrete $\sigma$-algebra, so every set of datasets is an event. No measurable structure on the data domain is assumed. The module also records that the published Laplace law `PrivLearn.Generic.laplace` is $\sigma$-finite.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), §2, p.7 (PDF p.9), and App. A, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

open MeasureTheory

namespace PFRelease

/-- Datasets of `n` slots over a domain `X` augmented with the null record `⊥`
(Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654, held version sha256 e1d516b3…, §2, p.7 = PDF p.9, and
App. A, p.26): a dataset `s = (s₁, …, sₙ) ∈ Xⁿ` is a sequence of `n` records, each occupying a slot.

**Formalization Note** A dataset is `Fin n → Option X`, with `none` the null record `⊥` and slots
indexed `0, …, n-1` (the paper's `1, …, n`). `Dataset X n` is a type synonym carrying the discrete
σ-algebra `⊤`, so that *every* set of datasets is an event when the laws of filtered datasets are
compared (Definition 3.3). No measurable structure on `X` is assumed, as in the paper. -/
def Dataset (X : Type*) (n : ℕ) : Type _ := Fin n → Option X

instance (X : Type*) (n : ℕ) : MeasurableSpace (Dataset X n) := ⊤

/-- `s^{I→⊥}`: the dataset obtained from `s` by nulling the records indexed by `I` (§2, p.7);
`s^{i→⊥}` is `nullOut s {i}`. -/
def nullOut {X : Type*} {n : ℕ} (s : Fin n → Option X) (I : Finset (Fin n)) : Fin n → Option X :=
  fun j => if j ∈ I then none else s j

/-- A dataset of `n` slots viewed as an element of `X* = ⋃ₙ Xⁿ`: the list of its records in slot
order, null records included (so `|toList s| = n`). -/
def toList {X : Type*} {n : ℕ} (s : Fin n → Option X) : List (Option X) := List.ofFn s

/-- `Lap(σ)` (the published `PrivLearn.Generic.laplace`) is σ-finite; needed to form product
noise laws. A structural instance. -/
instance laplace_sigmaFinite (σ : ℝ) : SigmaFinite (PrivLearn.Generic.laplace σ) := by
  unfold PrivLearn.Generic.laplace; infer_instance

end PFRelease


