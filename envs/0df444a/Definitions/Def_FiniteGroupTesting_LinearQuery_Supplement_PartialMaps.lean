-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_PartialMaps
-- name    : FiniteGroupTesting_LinearQuery_Supplement_PartialMaps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:16:12.983968+00:00
-- url     : https://prove2.me/theorems/c76d95ca-77bc-4d81-b572-1772c9f69a05
-- title:
--   Partial maps, multiplicativity and signed action defect
-- statement:
--   Let $G,H$ be finite sets, with a group structure on $H$ when multiplication is used. A partial map $\Psi:G\rightharpoonup H$ returns either a value of $H$ or an explicit undefined value. For $|G|=|H|=n>0$, define
--   $$\operatorname{defect}(\Psi)=1-\frac{|\operatorname{Im}\Psi|}{n}.$$
--   For an arbitrary operation $*$ on $G$, $\eta(\Psi)$ is the fraction of independent ordered pairs $(x,y)$ for which any required locator value is undefined or $\Psi(x*y)\ne\Psi(x)\Psi(y)$. Bijection error counts $\Psi(x)\ne\pi(x)$, including undefined values. Operation distance is the normalized count of disagreeing ordered pairs. A bijection $\pi$ transports multiplication by $x\circ y=\pi^{-1}(\pi(x)\pi(y))$.
--
--   Given $k$ marked elements $a_i$ of $H$, signed indices retain multiplicities and assign $a_{-i}=a_i^{-1}$. Conductance at least $\Phi$ means $|\partial S|\ge\Phi(2k)|S|$ for every nonempty $S$ with $2|S|\le n$. An action trial on arbitrary visible labels $u_j$ succeeds precisely when the two partial values are defined, $\Psi(x*u_j)=\Psi(x)a_j$, and $(x*u_j)*u_{-j}=x$. Its failure fraction is $\eta_{\rm act}$. These are reusable definitions; no group law is assumed for the input operation.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), pp. 28–32, Sections 4.5–4.6 and 5.1, 5.3

import Definitions.Def_FiniteGroupTesting_LinearQuery_TableModel
import Definitions.Def_FiniteGroupTesting_LinearQuery_RandomCayley

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Undefined values are genuinely absent, never a chosen element of H. -/
abbrev PartialMap (G H : Type*) := G → Option H

def imageSet {G H : Type*} [Fintype G] [Fintype H] (ψ : PartialMap G H) : Finset H :=
  Finset.univ.filter fun h => ∃ x, ψ x = some h

def defect {G H : Type*} [Fintype G] [Fintype H] (ψ : PartialMap G H) : ℝ :=
  1 - (imageSet ψ).card / (Fintype.card G : ℝ)

def bijectionError {G H : Type*} [Fintype G] (ψ : PartialMap G H) (π : G ≃ H) : ℝ :=
  uniformProbability fun x => ψ x ≠ some (π x)

def productGood {G H : Type*} [Mul H] (op : G → G → G) (ψ : PartialMap G H)
    (x y : G) : Prop := ∃ a b, ψ x = some a ∧ ψ y = some b ∧ ψ (op x y) = some (a * b)

def eta {G H : Type*} [Fintype G] [Mul H] (op : G → G → G) (ψ : PartialMap G H) : ℝ :=
  uniformProbability fun xy : G × G => ¬productGood op ψ xy.1 xy.2

def operationDistance {G : Type*} [Fintype G] (op law : G → G → G) : ℝ :=
  uniformProbability fun xy : G × G => op xy.1 xy.2 ≠ law xy.1 xy.2

def transport {G H : Type*} [Mul H] (π : G ≃ H) (x y : G) : G :=
  π.symm (π x * π y)

/-- Bool records sign; both occurrences of a repeated generator are counted. -/
abbrev Signed (k : ℕ) := Fin k × Bool

def reverseSign {k : ℕ} (j : Signed k) : Signed k := (j.1, !j.2)

def signedMark {H : Type*} [Group H] {k : ℕ} (a : Fin k → H) (j : Signed k) : H :=
  if j.2 then (a j.1)⁻¹ else a j.1

def boundary {H : Type*} [Fintype H] [Group H] {k : ℕ}
    (a : Fin k → H) (S : Finset H) : Finset (H × Signed k) :=
  Finset.univ.filter fun hj => hj.1 ∈ S ∧ hj.1 * signedMark a hj.2 ∉ S

/-- The lower-bound form of the minimum: every nonempty set of size at most n/2.
This avoids a default infimum when n=1. All uses of the minimum have n>=2, k>0. -/
def ConductanceAtLeast {H : Type*} [Fintype H] [Group H] {k : ℕ}
    (a : Fin k → H) (Φ : ℝ) : Prop :=
  ∀ S : Finset H, 0 < S.card → 2 * S.card ≤ Fintype.card H →
    Φ * (2 * k : ℝ) * S.card ≤ (boundary a S).card

def actionGood {G H : Type*} [Group H] {k : ℕ} (op : G → G → G)
    (u : Signed k → G) (a : Fin k → H) (ψ : PartialMap G H) (x : G) (j : Signed k) : Prop :=
  ∃ h, ψ x = some h ∧ ψ (op x (u j)) = some (h * signedMark a j) ∧
    op (op x (u j)) (u (reverseSign j)) = x

def etaAct {G H : Type*} [Fintype G] [Group H] {k : ℕ} (op : G → G → G)
    (u : Signed k → G) (a : Fin k → H) (ψ : PartialMap G H) : ℝ :=
  uniformProbability fun xj : G × Signed k => ¬actionGood op u a ψ xj.1 xj.2

end
end FiniteGroupTesting.LinearQuery.Supplement


