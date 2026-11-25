-- Prove2me | Definitions.Def_DetDLP_OpenAIAppendixD
-- name    : DetDLP_OpenAIAppendixD
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:55:55.111305+00:00
-- url     : https://prove2.me/theorems/ecb0f475-7d39-4e1d-bf96-947e13e6db6a
-- title:
--   OpenAI Appendix D.4 Cauchy–Hermite Contraction Premise
-- statement:
--   This premise records two interfaces from [OpenAI26, Appendix D, Section D.4, pp. 57–64]. Closed takes a schedule generator and a tensor-entry evaluator. One machine contracts every admissible closed network in polynomial space and in the time prescribed by the schedule and the entry cost. The generator supplies the schedule and the polynomial encoding on the instance input, so the contraction machine is uniform in the base modulus.
--
--   OneStep acts on the labeled graph before any tensor values or boundary assignments are supplied. It packs edges into packets and indexes the decomposition by retained Hermite nodes, interpolation points, and weighted modes. For every boundary assignment, the child contractions reproduce each local deformation, and their guarded Hermite sum recovers the scaled parent contraction. The interface also bounds mode counts and the cost of retrieving a branch record or evaluating a packet entry. The premise assumes both interfaces; it does not prove their existence.
-- source:
--   OpenAI (Oct 25, 2026), The Exponential Time Hypothesis is False, Appendix D, Section D.4, pp. 57–64

import Definitions.Def_DetDLP_ResidualScalarOracle

set_option autoImplicit false

namespace DetDLP
namespace AppendixD4
open Polynomial ResidualScalarOracle OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
noncomputable section

abbrev Bits := List Bool
abbrev Graph := BipartiteMultigraph
abbrev Tensor (G : Graph) (R : Type) := (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R

/-- Same coefficient ordering and framing as `F9A1.bEncode`. -/
def residue (f : ℤ[X]) (l p : ℕ) (hf : f.Monic) (x : B f l p) : Bits :=
  encodeNatListBin (List.ofFn fun k : Fin (l * f.natDegree) =>
    word f l p hf x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

/-- Reinterpret canonical integer coordinates, not a ring homomorphism. -/
def lift {f : ℤ[X]} {l p : ℕ} (hf : f.Monic) (q : ℕ) (x : B f l p) : B f l q :=
  AdjoinRoot.mk _ (∑ j : Fin l, monomial j.val (AdjoinRoot.mk _
    (∑ i : Fin f.natDegree, monomial i.val (word f l p hf x j i : ZMod (2^q)))))

def polynomialBits (f : ℤ[X]) : Bits :=
  List.ofFn fun i : Fin f.natDegree => decide (f.coeff i = 1)

def RingOK (f : ℤ[X]) : Prop :=
  0 < f.natDegree ∧ Irreducible (f.map (Int.castRingHom (ZMod 2))) ∧
    ∀ i < f.natDegree, f.coeff i = 0 ∨ f.coeff i = 1

/-- `X` gives the trivial, degree-one coefficient extension. -/
theorem ringOK_X : RingOK (X : ℤ[X]) := by
  refine ⟨by simp, by simpa using (irreducible_X : Irreducible (X : (ZMod 2)[X])), ?_⟩
  intro i hi
  have : i = 0 := by simpa using hi
  simp [this]

private def baseEquiv (P : ℕ) : ZMod (2^P) ≃+* U X P :=
  RingEquiv.ofBijective (AdjoinRoot.of _) (by
    let e := (quotientSpanXSubCAlgEquiv (0 : ZMod (2^P))).symm
    have h : Function.Bijective (AdjoinRoot.of (X - C (0 : ZMod (2^P)))) := e.bijective
    change Function.Bijective (AdjoinRoot.of ((X : ℤ[X]).map _))
    rw [Polynomial.map_X]
    rwa [show (X - C (0 : ZMod (2^P))) = X by simp] at h)

/-- Coefficientwise inclusion in the degree-one extension, leaving the truncation variable alone. -/
def truncPolyEquiv (P l : ℕ) : TruncPoly P l ≃+* B X l P :=
  AdjoinRoot.mapRingEquiv (baseEquiv P) (X^l) (X^l) (by simp)

private theorem truncCoeff {R : Type*} [CommRing R] {l : ℕ} (b : Fin l → R) (j : Fin l) :
    ((AdjoinRoot.modByMonicHom (monic_X_pow l) (AdjoinRoot.mk _
      (∑ i : Fin l, monomial i.val (b i)))).coeff j.val) = b j := by
  nontriviality R
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff (monic_X_pow l)).mpr]
  · simp only [finsetSum_coeff, coeff_monomial, Fin.val_eq_val, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [degree_X_pow]
    simp_rw [← C_mul_X_pow_eq_monomial]
    apply degree_sum_fin_lt

private theorem baseCoeff {P : ℕ} (b : ZMod (2^P)) :
    ((AdjoinRoot.modByMonicHom (monic_X.map _) (AdjoinRoot.of ((X : ℤ[X]).map (Int.castRingHom (ZMod (2^P)))) b)).coeff 0) = b := by
  nontriviality ZMod (2^P)
  rw [← AdjoinRoot.mk_C, AdjoinRoot.modByMonicHom_mk]
  rw [Polynomial.map_X, (modByMonic_eq_self_iff monic_X).mpr]
  · simp
  · exact (degree_C_le.trans_lt (by simp))

private theorem residue_ofCoeffs (P l : ℕ) (c : Fin l → ℕ) (hc : ∀ i, c i < 2^P) :
    residue X l P monic_X (truncPolyEquiv P l (truncPolyOfCoeffs P l c)) =
      encodeNatListBin (List.ofFn c) := by
  classical
  have he : truncPolyEquiv P l (truncPolyOfCoeffs P l c) = AdjoinRoot.mk _
      (∑ i : Fin l, monomial i.val (AdjoinRoot.of _ (c i : ZMod (2^P)))) := by
    change (AdjoinRoot.map (baseEquiv P).toRingHom (X^l) (X^l) (by simp)) (AdjoinRoot.mk _ (∑ i : Fin l, monomial i.val (c i : ZMod (2^P)))) = _
    simp only [map_sum, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X,
      AdjoinRoot.mk_C, AdjoinRoot.map_root,
      AdjoinRoot.map_of]
    rfl
  rw [he]
  unfold residue
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_ofFn]
    simp only [List.length_ofFn] at hj hj'
    change word X l P monic_X _ (finProdFinEquiv.symm (⟨j,hj⟩ : Fin (l*(X : ℤ[X]).natDegree))).1
      (finProdFinEquiv.symm (⟨j,hj⟩ : Fin (l*(X : ℤ[X]).natDegree))).2 = c ⟨j,hj'⟩
    unfold word
    rw [truncCoeff]
    have hi : (finProdFinEquiv.symm (⟨j,hj⟩ : Fin (l * (X : ℤ[X]).natDegree))).2.val = 0 := by
      have h := (finProdFinEquiv.symm (⟨j,hj⟩ : Fin (l * (X : ℤ[X]).natDegree))).2.isLt
      simpa using h
    rw [hi, baseCoeff, ZMod.val_natCast, Nat.mod_eq_of_lt (hc _)]
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv]

/-- The canonical residue bits coincide, not merely up to a recoding. -/
theorem encodesTruncPoly_iff_residue (P l : ℕ) (w : Bits) (z : TruncPoly P l) :
    EncodesTruncPoly P l w z ↔ w = residue X l P monic_X (truncPolyEquiv P l z) := by
  classical
  have repr : ∃ c : Fin l → ℕ, (∀ i, c i < 2^P) ∧ z = truncPolyOfCoeffs P l c := by
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective z
    let r := v %ₘ X^l
    refine ⟨fun i => ((r.coeff i).val), fun i => ZMod.val_lt _, ?_⟩
    unfold truncPolyOfCoeffs
    simp only [ZMod.natCast_zmod_val]
    change AdjoinRoot.mk _ v = AdjoinRoot.mk _ (∑ i : Fin l, monomial i.val (r.coeff i.val))
    rw [show (∑ i : Fin l, monomial i.val (r.coeff i.val)) = r from
      sum_modByMonic_coeff (monic_X_pow l) (degree_X_pow_le _)]
    exact (AdjoinRoot.mk_leftInverse (monic_X_pow l) (AdjoinRoot.mk _ v)).symm
  constructor
  · rintro ⟨c, hc, rfl, rfl⟩
    exact (residue_ofCoeffs P l c hc).symm
  · rintro rfl
    obtain ⟨c, hc, rfl⟩ := repr
    exact ⟨c, hc, residue_ofCoeffs P l c hc, rfl⟩

structure Schedule where
  H : ℕ
  start : ℕ
  D : ℕ
  cap : ℕ
  u : Fin D → ℕ
  a : Fin D → ℕ
  κ : ℕ

def Schedule.bits (s : Schedule) (f : ℤ[X]) : Bits := Encoding.encodeList id
  [encodeNatListBin [s.H, s.start, s.D, s.cap, s.κ], encodeNatListBin (List.ofFn s.u),
   encodeNatListBin (List.ofFn s.a), polynomialBits f]

def mult (M u : ℕ) := (3*M + u-1)/u
def points (M a : ℕ) := M * (2^(a+1)-1) + 1
def tileScale (a i : ℕ) := 2^(a-i)
def increase (M a u i : ℕ) := 8 * mult M u * tileScale a i + 8*M*(a+1)
def loss (M a u i : ℕ) := 6 * mult M u * tileScale a i + 4*M*(a+1)

/-- Worst previous-node increments, starting from the actual (possibly inherited) input
precision. No monotonicity or growth law for the caller's schedule is implicit. -/
def inherited (s : Schedule) (mass P d : ℕ) := P + ∑ j : Fin s.D,
  if j.val < d then increase (mass / 8^(s.start+j.val)) (s.a j) (s.u j) 0 else 0

def Active (s : Schedule) (mass P Bprec : ℕ) : Prop :=
  mass / 8^(s.start+s.D) ≤ s.H ∧ ∀ (d : Fin s.D) (M : ℕ),
    s.H < M → M ≤ mass / 8^(s.start+d.val) →
    let a := s.a d; let u := s.u d
    1 ≤ u ∧ u ≤ a ∧ u ≤ M ∧ 2*64^(4*a)*s.cap ≤ M ∧
    2^a * 64^(2*a) ≤ M ∧ 2*2^a ≤ s.cap ∧ points M a ≤ 2^s.κ ∧
    ∀ i < u, (inherited s mass P d.val + increase M a u i)*u ≤ Bprec*M*tileScale a i

def exponent (s : Schedule) (scale : ℕ) : ℝ := s.H + ∑ d : Fin s.D,
  ((scale : ℝ) / (8 : ℝ)^(s.start+d.val)) / Real.sqrt (s.u d : ℝ)

/-- The generator runs on the same input as the contraction machine and echoes the base
modulus with the schedule. The contraction machine is uniform in that modulus. -/
def Closed : Prop := ∀ (C c Bprec : ℕ), 0 < C → 0 < c → 0 < Bprec →
  ∀ (S E : PrimitiveMachine) (oS : Fin S.tapeCount) (oE : Fin E.tapeCount),
  ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (K : ℕ),
  ∀ (scale P l Told : ℕ) (desc : Bits) (G : Graph) (f : ℤ[X]) (hf : f.Monic)
    (T : Tensor G (B f l P)) (s : Schedule),
    2 ≤ scale → 1 ≤ Told → G.nE ≤ C*scale / 8^s.start → G.nV ≤ (scale+desc.length+1)^c →
    1 ≤ P → P ≤ (scale+1)^c → 1 ≤ l → l ≤ C*scale → RingOK f → f.natDegree ≤ (scale+1)^c →
    let n := scale + desc.length; let inp := encodeBTNInstance desc G scale P l
    RunsWithin S oS inp (s.bits f) (polyBound c n) (polyBound c n) →
    (∀ v α, RunsWithin E oE (encodePortQuery desc v.val (List.ofFn α))
      (residue f l P hf (T v α)) Told ((n : ℝ)^c)) →
    (s.H < G.nE → G.maxDeg ≤ s.cap ∧ s.cap ≤ C*scale ∧ 0 < s.κ ∧
      2^s.κ ≤ (scale+2)^c ∧ (f.natDegree = s.κ ∨ f.natDegree = 1) ∧
      Active s (C*scale) P Bprec) →
    RunsWithin A out inp (residue f l P hf (BTNContract G T))
      (polyBound K n * Told * (2 : ℝ)^((K : ℝ)*exponent s scale)) (polyBound K n)

/-- Orient by the bipartition, not by the arbitrary order of the stored endpoints. -/
def ends (G : Graph) (e : Fin G.nE) :=
  let p := G.endpoints e; if G.side p.1 then p.swap else p

abbrev Label (a : ℕ) (G : Graph) := Fin a → Fin G.nV → Fin 64

def Padded {G : Graph} {a : ℕ} (lbl : Label a G) : Prop := ∀ x y : Fin a → Fin 64,
  ((Finset.univ : Finset (Fin G.nE)).filter fun e =>
    (fun i => lbl i (ends G e).1) = x ∧ (fun i => lbl i (ends G e).2) = y).card +
    2^a ≤ 3*G.nE / 64^(2*a)

structure Packing {G : Graph} {a : ℕ} (lbl : Label a G) where
  count : ℕ
  bounded : count * 2^a ≤ 3*G.nE
  packet : Fin G.nE → Fin count
  slot : Fin G.nE → Fin (2^a)
  distinct : Function.Injective fun e => (packet e, slot e)
  symbols : Fin count → Fin a → Bool → Fin 64
  row : ∀ e i, lbl i (ends G e).1 = symbols (packet e) i ((slot e).val.testBit i.val)
  col : ∀ e i, lbl i (ends G e).2 = symbols (packet e) i (!((slot e).val.testBit i.val))

/-- Index `k` denotes the node `k-L`, in the complete residue grid. -/
def node {a : ℕ} (k : Fin (2^(a+1))) : ℤ := (k.val : ℤ) - 2^a
def level {a : ℕ} (k : Fin (2^(a+1))) := (node k).natAbs.factorization 2
abbrev Node (a u : ℕ) := {k : Fin (2^(a+1)) // node k ≠ 0 ∧ level k < u}

def coord {a u : ℕ} (hu : u ≤ a) (t : Node a u) : Fin a :=
  ⟨level t.val, lt_of_lt_of_le t.property.2 hu⟩

/-- (D.7) with its removable factor cancelled before any substitution. -/
def kernel (a : ℕ) (x y : Fin (2^a)) : ℚ[X] :=
  let grid := (Finset.univ : Finset (Fin (2^(a+1))))
  let den : ℚ := ∏ k ∈ grid.filter (fun k => node k ≠ 0), -(node k : ℚ)
  C den⁻¹ * ∏ k ∈ grid.filter (fun k => node k ≠ (y.val : ℤ)-x.val), (X-C (node k : ℚ))

def point (f : ℤ[X]) (q k : ℕ) : U f q := AdjoinRoot.mk _
  (∑ i : Fin f.natDegree, monomial i.val (if k.testBit i.val then 1 else 0))

/-- D.4 evaluates the integral *local polynomial* at a binary-coordinate lift. In
particular this does not attempt to invert `C'(0)` in a ring of even characteristic. -/
def localW (f : ℤ[X]) (a q : ℕ) (t : ℤ) (k : ℕ) (x y : Fin (2^a)) : U f q :=
  let poly := (kernel a x y).comp (C (t : ℚ) + C (2^(a+1)) * X)
  ∑ j ∈ poly.support, let c := poly.coeff j
    (c.num : U f q) * Ring.inverse (c.den : U f q) * point f q k ^ j

abbrev Pins {G : Graph} {b : ℕ} (host : Fin b → Fin G.nV) (v : Fin G.nV) :=
  {j : Fin b // host j = v} → Bool
abbrev OpenTensor {G : Graph} {b : ℕ} (host : Fin b → Fin G.nV) (R : Type) :=
  (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Pins host v → R

def pin {G : Graph} {b : ℕ} {host : Fin b → Fin G.nV} {R : Type}
    (T : OpenTensor host R) (η : Fin b → Bool) : Tensor G R :=
  fun v α => T v α (fun j => η j.val)

def affine {R : Type} [Ring R] (bit : Bool) (z : R) := if bit then z else 1-z

/-- (D.8) at a retained node and interpolation point, with independent port bits. -/
def deformation {G : Graph} {a : ℕ} {lbl : Label a G} (pk : Packing lbl)
    {f : ℤ[X]} {l p : ℕ} (hf : f.Monic) (q : ℕ) (t : ℤ) (k : ℕ) (T : Tensor G (B f l p)) :=
  ∑ Xb : Fin G.nE → Bool, ∑ Yb : Fin G.nE → Bool,
    (∏ v, lift hf q (T v fun j => (if G.side v then Xb else Yb) ((G.ports v).get j))) *
    ∏ x, affine (Yb x) (∑ y, if pk.packet x = pk.packet y ∧ Xb y then
      AdjoinRoot.of _ (localW f a q t k (pk.slot x) (pk.slot y)) else 0 : B f l q)

/-- Each old port is addressed in its original local order; packet vertices have no
argument for external bits. Thus `pin` commutes with forming every child. -/
structure Child {G : Graph} {a : ℕ} {lbl : Label a G} (pk : Packing lbl) (i : Fin a)
    (g : Fin 64) (R : Type) where
  graph : Graph
  oldOrPacket : Fin graph.nV ≃ ({v : Fin G.nV // lbl i v = g} ⊕ Fin pk.count)
  side : ∀ v, graph.side v = (oldOrPacket v).isRight
  ports : ∀ v : {v : Fin G.nV // lbl i v = g},
    Fin (G.deg v.val) ≃ Fin (graph.deg (oldOrPacket.symm (.inl v)))
  incidence : ∀ v j, let w := oldOrPacket.symm (.inl v)
    let e := (graph.ports w).get (ports v j)
    oldOrPacket (ends graph e).2 = .inr (pk.packet ((G.ports v.val).get j))
  packetDeg : ∀ r, graph.deg (oldOrPacket.symm (.inr r)) ≤ 2*2^a
  edges : graph.nE ≤ 3*G.nE/32
  descriptor : Fin pk.count → Bits
  entry : ∀ r, (Fin (graph.deg (oldOrPacket.symm (.inr r))) → Bool) → R

def Child.tensor {G : Graph} {a : ℕ} {lbl : Label a G} {pk : Packing lbl} {i g}
    {R R' : Type} (c : Child pk i g R') (up : R → R') (T : Tensor G R) : Tensor c.graph R' :=
  let atVertex : (z : _) → (Fin (c.graph.deg (c.oldOrPacket.symm z)) → Bool) → R'
    | .inl v => fun α => up (T v.val (α ∘ c.ports v))
    | .inr r => c.entry r
  fun w => (c.oldOrPacket.symm_apply_apply w) ▸ atVertex (c.oldOrPacket w)

def Child.bits {G : Graph} {a : ℕ} {lbl : Label a G} {pk : Packing lbl} {i g}
    {R : Type} (c : Child pk i g R) : Bits := Encoding.encodeList id [c.graph.encode,
  Encoding.encodeList id (List.ofFn fun w => match c.oldOrPacket w with
    | .inl v => Encoding.encodeList id [[false], countWord v.val.val, encodeNatListBin
        (List.ofFn fun j => (c.ports v j).val)]
    | .inr r => Encoding.encodeList id [[true], countWord r.val, c.descriptor r])]

/-- Exponent tuples of (D.14), with a random-access ordering. Ranks may be computed by
counting suffixes for each remaining integer budget (a polynomial-size dynamic program). -/
structure Modes (M D q : ℕ) where
  vars : ℕ
  weight : Fin vars → ℕ
  pos : ∀ z, 0 < weight z ∧ weight z < q
  density : ∀ w, ((Finset.univ : Finset (Fin vars)).filter fun z => weight z = w).card * D ≤ 6*M
  count : ℕ
  tuples : Fin count ≃ {β : Fin vars → Fin q // ∑ z, weight z * (β z).val < q}

structure Step {G : Graph} {a u : ℕ} (lbl : Label a G) (hu : u ≤ a) (f : ℤ[X]) (l p : ℕ) where
  pk : Packing lbl
  modes : (t : Node a u) → Modes G.nE (tileScale a (level t.val))
    (p + increase G.nE a u (level t.val))
  weight : Node a u → Fin (points G.nE a) → U f (p + loss G.nE a u 0)
  weight_guard : ∀ t k, (2 : U f (p + loss G.nE a u 0))^
    (loss G.nE a u 0 - loss G.nE a u (level t.val)) ∣ weight t k
  child : (t : Node a u) → Fin (points G.nE a) → Fin (modes t).count → (g : Fin 64) →
    Child pk (coord hu t) g (B f l (p + increase G.nE a u (level t.val)))
  mass : ∀ t k β, (∑ g, (child t k β g).graph.nE) = 2*G.nE

variable {G : Graph} {a u : ℕ} {lbl : Label a G} {hu : u ≤ a} {f : ℤ[X]} {l p : ℕ}

abbrev Branch (s : Step lbl hu f l p) :=
  (t : Node a u) × Fin (points G.nE a) × Fin (s.modes t).count

/-- The guarded equality uses canonical lifts of *each* child, not a fictitious
common child creation precision. The step (in particular all its Hermite weights) is
fixed before the open tensor, host map, and boundary assignment are quantified. -/
def Step.sound (s : Step lbl hu f l p) (hf : f.Monic) : Prop :=
  ∀ (b : ℕ) (host : Fin b → Fin G.nV) (T : OpenTensor host (B f l p)) (η : Fin b → Bool),
    let old := pin T η
    let Z := fun t k β g => let c := s.child t k β g
                            BTNContract c.graph (c.tensor (lift hf _) old)
    let guard := loss G.nE a u 0
    (∀ t k, deformation s.pk hf (p + increase G.nE a u (level t.val)) (node t.val) k.val old =
        ∑ β, ∏ g, Z t k β g) ∧
    (∑ ν : Branch s, AdjoinRoot.of _ (s.weight ν.1 ν.2.1) *
      ∏ g, lift hf (p+guard) (Z ν.1 ν.2.1 ν.2.2 g)) =
      2^guard * lift hf (p+guard) (BTNContract G old)

/-- The structural input does not contain tensor values or boundary assignments. A
consumer restricts `host` at the returned coordinate using the old-vertex identifiers. -/
def stepInput (G : Graph) (a u p l : ℕ) (f : ℤ[X]) (lbl : Label a G) := Encoding.encodeList id
  [G.encode, encodeNatListBin [a,u,p,l], polynomialBits f,
   encodeNatListBin ((List.finRange a).flatMap fun i => List.ofFn fun v => (lbl i v).val)]

def Step.bits (s : Step lbl hu f l p) (hf : f.Monic) (ν : Branch s) : Bits :=
  let t := ν.1; let k := ν.2.1; let β := ν.2.2
  Encoding.encodeList id [encodeNatListBin [t.val.val,k.val,β.val,level t.val,
    p + increase G.nE a u (level t.val)],
    residue f l (p + loss G.nE a u 0) hf (AdjoinRoot.of _ (s.weight t k)),
    encodeNatListBin (List.ofFn fun z => ((s.modes t).tuples β).val z |>.val),
    Encoding.encodeList id (List.ofFn fun g => (s.child t k β g).bits)]

/-- Query 0 returns the branch count; query j+1 returns the record of branch j. -/
def OneStep : Prop := ∃ (A E : PrimitiveMachine) (oA : Fin A.tapeCount) (oE : Fin E.tapeCount)
    (K : ℕ), ∀ (G : Graph) (a u p l : ℕ) (f : ℤ[X]) (hf : f.Monic) (lbl : Label a G),
    1 ≤ u → (hu : u ≤ a) → u ≤ G.nE → 1 ≤ l → 1 ≤ p → RingOK f →
    points G.nE a ≤ 2^f.natDegree → 2^a * 64^(2*a) ≤ G.nE → Padded lbl →
    ∃ (s : Step lbl hu f l p) (order : Fin (Fintype.card (Branch s)) ≃ Branch s),
    let M := G.nE; let n := M + p + f.natDegree + l + 2
    let inp := stepInput G a u p l f lbl; let bound := polyBound K (n+inp.length)
    s.sound hf ∧ (∀ t, ((s.modes t).count : ℝ) ≤ Real.exp ((K : ℝ)*Real.sqrt
      ((M : ℝ) * (p + increase M a u (level t.val)) / tileScale a (level t.val)))) ∧
    RunsWithin A oA (Encoding.encodeList id [inp,countWord 0]) (countWord (Fintype.card (Branch s)))
      bound bound ∧ (∀ j, RunsWithin A oA (Encoding.encodeList id [inp,countWord (j.val+1)])
        (s.bits hf (order j)) bound bound) ∧
    ∀ t k β g r α, let c := s.child t k β g
      RunsWithin E oE (Encoding.encodeList id [c.descriptor r,List.ofFn α])
        (residue f l _ hf (c.entry r α))
        (Real.exp ((K : ℝ)*(2^a : ℕ)*Real.log n)) (polyBound K n)

end
end AppendixD4

/-- Interfaces extracted from the closed recursion and its local algebra in Appendix D.4.
This is a premise type; declaring it does not supply a proof of the external algorithm. -/
structure OpenAIAppendixDPremise : Prop where
  closed_schedule_contraction : AppendixD4.Closed
  one_step_packet_hermite_mode : AppendixD4.OneStep

end DetDLP


