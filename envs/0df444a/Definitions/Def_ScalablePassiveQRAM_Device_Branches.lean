-- Prove2me | Definitions.Def_ScalablePassiveQRAM_Device_Branches
-- name    : ScalablePassiveQRAM_Device_Branches
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:50:23.154519+00:00
-- url     : https://prove2.me/theorems/e810e54e-a452-4c0e-a8ab-d412b38956bb
-- title:
--   History-path and two-address tensor identifications
-- statement:
--   The path Hamiltonian is a tridiagonal matrix with the perfect-transfer weights. The history embedding sends each path basis vector to its computed physical configuration. For two addresses, the outside factor contains every configuration outside their combined footprints, with no vacancy or product-state restriction there.
--
--   $$\mathcal S_z^{xy}=\operatorname{span}\{|\widehat\Phi_j(z,b)\rangle\}_{j,b}\otimes|\circ\rangle_{F_{xy}\setminus F_z}\otimes\mathcal H_{\rm aux\setminus F_{xy}}.$$
--
--   The tensor embedding is constructed by inserting the computed history inside the union and the arbitrary outside configuration elsewhere. Outside operators are actual compressions of the physical Hamiltonian to a vacuum interior. The definitions also form arbitrary off-diagonal address inputs with unrestricted bus-reference and outside operators for equation (58). No separation identity is assumed.
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), §§3.3,4.1, equations (25)–(29),(53)–(58), pp.17–19,27–28. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Static
import Mathlib

noncomputable section
open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000

namespace ScalablePassiveQRAM.Device
local instance branchDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance branchDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

abbrev Path (n : ℕ) := Fin (length n+1)

def pathHamiltonian (L : ℕ) (Ω : ℝ) : Op (Fin (L+1)) :=
  ∑ j : Fin L, ((Ω / 2 * Real.sqrt (((j.val+1 : ℕ) : ℝ) * ((L-j.val : ℕ) : ℝ)) : ℝ) : ℂ) •
    (outer (ket (⟨j.val+1,by omega⟩ : Fin (L+1))) (ket ⟨j.val,by omega⟩) +
     outer (ket (⟨j.val,by omega⟩ : Fin (L+1))) (ket ⟨j.val+1,by omega⟩))

def phase (L : ℕ) : ℝ := -Real.pi * L / 2

def historyEmbedding (n : ℕ) (x : Address n) (b : Bool) (D : Database n) :
    Matrix (Basis n) (Path n) ℂ := fun i j => history n j x b D i

/-- Zero/one carrier flavors and the expected port and switch contents are computed from the prefix. -/
def exchanged (n j : ℕ) (port : ExchangePort) (into : Bool) : Bool :=
  ((schedule n).take j).any fun op => match op with
  | .exchange r b _ => r == port && b == into
  | _ => false

def portContents (n j : ℕ) (x : Address n) (b : Bool) (D : Database n) : PortBasis n :=
  fun (k,c) =>
    let r := if k.val < n then ExchangePort.address k.val else .bus
    if exchanged n j r true && !(exchanged n j r false) then false
    else c == (if h : k.val < n then x ⟨k.val,h⟩
      else if exchanged n j .bus false then xor b (D x) else b)

def switchContents (n j : ℕ) (x : Address n) : Switch n → Bool :=
  fun ⟨d,v,r,c⟩ =>
    decide (v = (fun i => bits n x i.val)) &&
    exchanged n j (.switch d 0) false &&
    !(exchanged n j (.switch d (visits n d)) true) &&
    decide (r.val = routeCount n j d) && (c == bits n x d)

abbrev Outside (n : ℕ) (x y : Address n) :=
  {q : Auxiliary n // (.inr (.inl q) : Qubit n) ∉ footprint n x ∪ footprint n y}
abbrev OutsideBasis (n : ℕ) (x y : Address n) := Outside n x y → Bool

/-- Compression to vacuum on both footprints, with arbitrary outside configurations. -/
def outsideConfig (n : ℕ) (x y : Address n) (o : OutsideBasis n x y) : AuxBasis n :=
  fun q => if h : q ∈ {q | (.inr (.inl q) : Qubit n) ∉ footprint n x ∪ footprint n y} then
    o ⟨q,h⟩ else false

def outsideH (n : ℕ) (Ω : ℝ) (D : Database n) (x y : Address n) : Op (OutsideBasis n x y) :=
  fun a b => sectorMatrix n D (hamiltonian n Ω)
    ((fun _ => false),outsideConfig n x y a) ((fun _ => false),outsideConfig n x y b)

def outsideP (n : ℕ) (Δ : ℝ) (x y : Address n) : Op (OutsideBasis n x y) :=
  fun a b => if a = b then ∑ q : Outside n x y,
    if a q then (Δ * pinningWeight (.inr (.inl q.val)) : ℂ) else 0 else 0

def pairConfig (n : ℕ) (D : Database n) (x y z : Address n) (j : Path n) (b : Bool)
    (o : OutsideBasis n x y) : Sector n :=
  let h := historyConfig n j z b D
  ((fun q => h (.inl q)), fun q =>
    if ht : (.inr (.inl q) : Qubit n) ∉ footprint n x ∪ footprint n y then o ⟨q,ht⟩
    else h (.inr (.inl q)))

/-- Range is exactly the tensor subspace (54), including both initial bus values. -/
def pairEmbedding (n : ℕ) (D : Database n) (x y z : Address n) :
    Matrix (Sector n) ((Path n × Bool) × OutsideBasis n x y) ℂ :=
  fun i j => if i = pairConfig n D x y z j.1.1 j.1.2 j.2 then 1 else 0

def pairGenerator (n : ℕ) (Ω : ℝ) (D : Database n) (x y : Address n) :
    Op ((Path n × Bool) × OutsideBasis n x y) :=
  fun i j =>
    (if i.1.2 = j.1.2 ∧ i.2 = j.2 then pathHamiltonian (length n) Ω i.1.1 j.1.1 else 0) +
    (if i.1 = j.1 then outsideH n Ω D x y i.2 j.2 else 0)

def pairPinning (n : ℕ) (Δ : ℝ) (x y : Address n) :
    Op ((Path n × Bool) × OutsideBasis n x y) :=
  fun i j => (if i = j then (((n+2 : ℕ) : ℝ) * Δ : ℂ) else 0) +
    if i.1 = j.1 then outsideP n Δ x y i.2 j.2 else 0

/-- Arbitrary off-diagonal address block and arbitrary outside operator, as in (58). -/
def pairInput (n r : ℕ) (D : Database n) (x y : Address n)
    (Z : Op (Bool × Fin r)) (ω : Op (OutsideBasis n x y)) : Op (Sector n × Fin r) :=
  fun i j => ∑ b : Bool, ∑ c : Bool, ∑ a : OutsideBasis n x y, ∑ d : OutsideBasis n x y,
    if i.1 = pairConfig n D x y x ⟨0,by omega⟩ b a ∧
       j.1 = pairConfig n D x y y ⟨0,by omega⟩ c d then Z (b,i.2) (c,j.2) * ω a d else 0

def pairOutput (n r : ℕ) (Ω Δ : ℝ) (D : Database n)
    (X : Op (Sector n × Fin r)) : Op (Logical n × Fin r) :=
  let U := evolve (sectorHamiltonian n Ω Δ D) (Real.pi / Ω)
  let Y : Op (Sector n × Fin r) := fun i j =>
    conjugate U (fun a b => X (a,i.2) (b,j.2)) i.1 j.1
  decode n (fun i j => ∑ a : AuxBasis n, Y ((i.1,a),i.2) ((j.1,a),j.2))

end ScalablePassiveQRAM.Device


