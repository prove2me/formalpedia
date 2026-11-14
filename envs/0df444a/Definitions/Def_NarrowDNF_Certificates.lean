-- Prove2me | Definitions.Def_NarrowDNF_Certificates
-- name    : NarrowDNF_Certificates
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:22.32775+00:00
-- url     : https://prove2.me/theorems/43e6f70e-6e4f-4635-8665-4ce943d65e34
-- title:
--   Positive terms, active-one certificates, and the finite family of short certificates
-- statement:
--   For a finite coordinate set $I$, a positive term indexed by $T\subseteq I$ holds at $x\in\{0,1\}^I$ when every coordinate in $T$ is one. A finite positive DNF holds when at least one of its terms holds. The empty conjunction is true and the empty disjunction is false.
--
--   For a local activation family $J$, let $A_J(x)$ be its active union and define
--   $$T_J(x)=\{i\in A_J(x):x_i=1\}.$$
--   The bundle represents $A_J(x)$ as a finite set and calls $T_J(x)$ the certificate. This name alone does not assert that it certifies acceptance; the appropriate monotonicity and adaptive-measurability hypotheses are used in later proofs of that property.
--
--   Given a Boolean readout $u$ and natural cutoff $w$, the truncated term family is exactly
--   $$\{T_J(x):u(x)=1,\ |T_J(x)|\le w\}.$$
--   It is a finite image of qualifying accepted inputs, so repeated copies of the same term are removed. This constructs concrete positive DNFs for the final width approximation.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Certificates.lean#L36-L37
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Certificates.lean#L9-L10
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Certificates.lean#L70-L76
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Certificates.lean#L12-L14
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Certificates.lean#L33-L34

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Monotone.Basic
import Definitions.Def_NarrowDNF_Adaptive

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation


namespace NarrowDNF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive conjunction, including the true empty conjunction. -/
def TermHolds (T : Finset ι) (x : Cube ι) : Prop := ∀ i ∈ T, x i = true

/-- A finite monotone DNF, including the false empty disjunction. -/
def DNFHolds (terms : Finset (Finset ι)) (x : Cube ι) : Prop :=
  ∃ T ∈ terms, TermHolds T x





namespace Activation

noncomputable def activeFinset (J : Activation ι) (x : Cube ι) : Finset ι :=
  by classical exact Finset.univ.filter fun i => i ∈ J.active x

noncomputable def certificate (J : Activation ι) (x : Cube ι) : Finset ι :=
  by classical exact (J.activeFinset x).filter fun i => x i = true











/-- Keep exactly the certificates of accepted inputs whose certificate has
cardinality at most the cutoff. This explicitly constructs a finite DNF. -/
noncomputable def truncatedTerms (J : Activation ι) (u : Cube ι → Bool)
    (w : ℕ) : Finset (Finset ι) :=
  by
    classical
    exact (Finset.univ.filter fun x => u x = true ∧ (J.certificate x).card ≤ w).image J.certificate









end Activation
end NarrowDNF


