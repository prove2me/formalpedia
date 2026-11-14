-- Prove2me | Definitions.Def_NarrowDNF_Adaptive
-- name    : NarrowDNF_Adaptive
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:58:55.998703+00:00
-- url     : https://prove2.me/theorems/1b5c6b88-f2a0-4126-ab35-9ba3ec2cfb0b
-- title:
--   Local activation families and the information retained by adaptive atoms
-- statement:
--   For a coordinate index type $I$, write $\operatorname{Cube}(I)=\{0,1\}^I$. An activation family assigns a predicate $J_S(x)$ to every finite $S\subseteq I$, together with locality: if $x$ and $y$ agree on $S$, then $J_S(x)\leftrightarrow J_S(y)$. Thus the global-input representation of $J_S$ gives the test no access to coordinates outside $S$.
--
--   The family is increasing when every predicate $J_S$ is monotone in the coordinatewise order. Its active union at $x$ is
--   $$A_J(x)=\bigcup_{S:J_S(x)}S.$$
--   Two inputs belong to the same adaptive atom precisely when their active unions coincide and their original labels agree on that common union. A Boolean readout is measurable for this adaptive information when it is constant on each such atom. Finally, $\operatorname{zeroOutside}(J,x)$ agrees with $x$ on $A_J(x)$ and is zero elsewhere. These objects record input-dependent coordinate information; they do not impose a fixed-coordinate junta restriction.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Adaptive.lean#L41-L42
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Adaptive.lean#L11-L11
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Adaptive.lean#L13-L15
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Adaptive.lean#L20-L20
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Adaptive.lean#L22-L23
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Adaptive.lean#L25-L26
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Adaptive.lean#L28-L29

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Monotone.Basic

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation


/-! Local activation families and their adaptive atoms. The global-input encoding
of a local activation carries an explicit locality proof, so it does not grant
an activation access to coordinates outside its indexing set. -/
namespace NarrowDNF

abbrev Cube (ι : Type*) := ι → Bool

structure Activation (ι : Type*) where
  fires : Finset ι → Cube ι → Prop
  locality : ∀ S x y, (∀ i ∈ S, x i = y i) → (fires S x ↔ fires S y)

namespace Activation
variable {ι : Type*} [DecidableEq ι]

def Increasing (J : Activation ι) : Prop := ∀ S, Monotone (J.fires S)

def active (J : Activation ι) (x : Cube ι) : Set ι :=
  {i | ∃ S, i ∈ S ∧ J.fires S x}

def SameAtom (J : Activation ι) (x y : Cube ι) : Prop :=
  J.active x = J.active y ∧ ∀ i ∈ J.active x, x i = y i

def Measurable (J : Activation ι) (u : Cube ι → Bool) : Prop :=
  ∀ x y, J.SameAtom x y → u x = u y





noncomputable def zeroOutside (J : Activation ι) (x : Cube ι) : Cube ι :=
  by classical exact fun i => if i ∈ J.active x then x i else false







end Activation
end NarrowDNF


