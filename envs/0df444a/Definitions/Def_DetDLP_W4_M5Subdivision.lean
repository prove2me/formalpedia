-- Prove2me | Definitions.Def_DetDLP_W4_M5Subdivision
-- name    : DetDLP_W4_M5Subdivision
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:31:08.388396+00:00
-- url     : https://prove2.me/theorems/fc15970c-4b34-4274-83a0-4a1ad66101ae
-- title:
--   Wire subdivision and ordered Boolean ports
-- statement:
--   Replaces each wire with two half-wires and an equality check. Proves that this preserves unique satisfying extensions and controls degrees.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP.w4_M5Network

/-- An unoriented wire network before imposing bipartiteness. Parallel wires are
    allowed. The two ends of every wire are distinct. -/
structure WireGraph where
  nV : ℕ
  nE : ℕ
  endpoints : Fin nE → Fin nV × Fin nV
  loopless : ∀ e, (endpoints e).1 ≠ (endpoints e).2

namespace WireGraph

def ports (G : WireGraph) (v : Fin G.nV) : List (Fin G.nE) :=
  (List.finRange G.nE).filter
    (fun e => decide ((G.endpoints e).1 = v ∨ (G.endpoints e).2 = v))

def deg (G : WireGraph) (v : Fin G.nV) : ℕ := (G.ports v).length

@[simp] theorem mem_ports (G : WireGraph) (v : Fin G.nV) (e : Fin G.nE) :
    e ∈ G.ports v ↔ (G.endpoints e).1 = v ∨ (G.endpoints e).2 = v := by
  simp [ports]

/-- Each original wire is replaced by two half-wires and one equality vertex.
    The first block of vertices consists of original vertices, and the second
    consists of equality vertices. -/
def subdivision (G : WireGraph) : BipartiteMultigraph where
  nV := G.nV + G.nE
  nE := G.nE + G.nE
  endpoints := Fin.addCases
    (fun e => (Fin.castAdd G.nE (G.endpoints e).1, Fin.natAdd G.nV e))
    (fun e => (Fin.castAdd G.nE (G.endpoints e).2, Fin.natAdd G.nV e))
  side := Fin.addCases (fun _ => false) (fun _ => true)
  bipartite := by
    intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e <;>
      simp only [Fin.addCases_left, Fin.addCases_right] <;> decide

@[simp] theorem subdivision_nV (G : WireGraph) :
    G.subdivision.nV = G.nV + G.nE := rfl

@[simp] theorem subdivision_nE (G : WireGraph) :
    G.subdivision.nE = 2 * G.nE := by simp [subdivision]; omega

end WireGraph

namespace PortLookup

@[simp] theorem mem_ports (G : BipartiteMultigraph) (v : Fin G.nV) (e : Fin G.nE) :
    e ∈ G.ports v ↔ (G.endpoints e).1 = v ∨ (G.endpoints e).2 = v := by
  simp [BipartiteMultigraph.ports]

/-- Locate a specified incident edge in the target's increasing-index port list. -/
def index (G : BipartiteMultigraph) (v : Fin G.nV) (e : Fin G.nE)
    (h : (G.endpoints e).1 = v ∨ (G.endpoints e).2 = v) : Fin (G.deg v) :=
  ⟨(G.ports v).idxOf e, List.idxOf_lt_length_of_mem ((mem_ports G v e).2 h)⟩

@[simp] theorem get_index (G : BipartiteMultigraph) (v : Fin G.nV) (e : Fin G.nE)
    (h : (G.endpoints e).1 = v ∨ (G.endpoints e).2 = v) :
    (G.ports v).get (index G v e h) = e := by
  exact List.idxOf_get _

end PortLookup

namespace WireGraph

def leftHalf (G : WireGraph) (e : Fin G.nE) : Fin G.subdivision.nE :=
  Fin.castAdd G.nE e

def rightHalf (G : WireGraph) (e : Fin G.nE) : Fin G.subdivision.nE :=
  Fin.natAdd G.nE e

def oldVertex (G : WireGraph) (v : Fin G.nV) : Fin G.subdivision.nV :=
  Fin.castAdd G.nE v

def equalityVertex (G : WireGraph) (e : Fin G.nE) : Fin G.subdivision.nV :=
  Fin.natAdd G.nV e

@[simp] theorem endpoints_leftHalf (G : WireGraph) (e : Fin G.nE) :
    G.subdivision.endpoints (G.leftHalf e) =
      (G.oldVertex (G.endpoints e).1, G.equalityVertex e) := by
  simp only [subdivision, leftHalf, oldVertex, equalityVertex, Fin.addCases_left]

@[simp] theorem endpoints_rightHalf (G : WireGraph) (e : Fin G.nE) :
    G.subdivision.endpoints (G.rightHalf e) =
      (G.oldVertex (G.endpoints e).2, G.equalityVertex e) := by
  simp only [subdivision, rightHalf, oldVertex, equalityVertex, Fin.addCases_right]

/-- The half-wire incident to a given original vertex. -/
def incidentHalf (G : WireGraph) (v : Fin G.nV) (e : Fin G.nE) :
    Fin G.subdivision.nE :=
  if (G.endpoints e).1 = v then G.leftHalf e else G.rightHalf e

theorem incidentHalf_incident (G : WireGraph) (v : Fin G.nV) (e : Fin G.nE)
    (h : e ∈ G.ports v) :
    (G.subdivision.endpoints (G.incidentHalf v e)).1 = G.oldVertex v ∨
      (G.subdivision.endpoints (G.incidentHalf v e)).2 = G.oldVertex v := by
  apply Or.inl
  unfold incidentHalf
  split
  · rename_i hfirst
    rw [endpoints_leftHalf, hfirst]
  · rename_i hfirst
    have hsecond := ((mem_ports G v e).1 h).resolve_left hfirst
    rw [endpoints_rightHalf, hsecond]

/-- Reorder a target local word into the original network's port order. -/
def oldPort (G : WireGraph) (v : Fin G.nV) (i : Fin (G.deg v)) :
    Fin (G.subdivision.deg (G.oldVertex v)) :=
  PortLookup.index _ _ (G.incidentHalf v ((G.ports v).get i))
    (G.incidentHalf_incident v _ (List.get_mem _ _))

@[simp] theorem get_oldPort (G : WireGraph) (v : Fin G.nV) (i : Fin (G.deg v)) :
    (G.subdivision.ports (G.oldVertex v)).get (G.oldPort v i) =
      G.incidentHalf v ((G.ports v).get i) := by
  exact PortLookup.get_index _ _ _ _

def equalityLeftPort (G : WireGraph) (e : Fin G.nE) :
    Fin (G.subdivision.deg (G.equalityVertex e)) :=
  PortLookup.index _ _ (G.leftHalf e) (by exact Or.inr (by rw [endpoints_leftHalf]))

def equalityRightPort (G : WireGraph) (e : Fin G.nE) :
    Fin (G.subdivision.deg (G.equalityVertex e)) :=
  PortLookup.index _ _ (G.rightHalf e) (by exact Or.inr (by rw [endpoints_rightHalf]))

/-- A tensor at an original vertex reads the same wires as before. A new vertex
    checks equality of the two halves of its wire. -/
def subdivisionTensor (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool) :
    (v : Fin G.subdivision.nV) → (Fin (G.subdivision.deg v) → Bool) → Bool :=
  Fin.addCases
    (fun v α => T v (fun i => α (G.oldPort v i)))
    (fun e α => decide (α (G.equalityLeftPort e) = α (G.equalityRightPort e)))

/-- Duplicate each wire value onto its two halves. -/
def liftAssignment (G : WireGraph) (x : Fin G.nE → Bool) :
    Fin G.subdivision.nE → Bool := Fin.addCases x x

@[simp] theorem lift_leftHalf (G : WireGraph) (x : Fin G.nE → Bool) (e : Fin G.nE) :
    G.liftAssignment x (G.leftHalf e) = x e := by
  simp only [liftAssignment, leftHalf, Fin.addCases_left]

@[simp] theorem lift_rightHalf (G : WireGraph) (x : Fin G.nE → Bool) (e : Fin G.nE) :
    G.liftAssignment x (G.rightHalf e) = x e := by
  simp only [liftAssignment, rightHalf, Fin.addCases_right]

@[simp] theorem lift_incidentHalf (G : WireGraph) (x : Fin G.nE → Bool)
    (v : Fin G.nV) (e : Fin G.nE) :
    G.liftAssignment x (G.incidentHalf v e) = x e := by
  unfold incidentHalf
  split <;> simp

/-- Satisfaction of the original network. -/
def Satisfies (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (x : Fin G.nE → Bool) : Prop :=
  ∀ v, T v (fun i => x ((G.ports v).get i)) = true

def SubdivisionSatisfies (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (x : Fin G.subdivision.nE → Bool) : Prop :=
  ∀ v, G.subdivisionTensor T v (fun i => x ((G.subdivision.ports v).get i)) = true

@[simp] theorem subdivisionTensor_oldVertex (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (v : Fin G.nV) (α : Fin (G.subdivision.deg (G.oldVertex v)) → Bool) :
    G.subdivisionTensor T (G.oldVertex v) α = T v (fun i => α (G.oldPort v i)) := by
  simp only [subdivisionTensor, oldVertex, Fin.addCases_left]

@[simp] theorem subdivisionTensor_equalityVertex (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (e : Fin G.nE) (α : Fin (G.subdivision.deg (G.equalityVertex e)) → Bool) :
    G.subdivisionTensor T (G.equalityVertex e) α =
      decide (α (G.equalityLeftPort e) = α (G.equalityRightPort e)) := by
  simp only [subdivisionTensor, equalityVertex, Fin.addCases_right]

@[simp] theorem get_equalityLeftPort (G : WireGraph) (e : Fin G.nE) :
    (G.subdivision.ports (G.equalityVertex e)).get (G.equalityLeftPort e) = G.leftHalf e := by
  exact PortLookup.get_index _ _ _ _

@[simp] theorem get_equalityRightPort (G : WireGraph) (e : Fin G.nE) :
    (G.subdivision.ports (G.equalityVertex e)).get (G.equalityRightPort e) = G.rightHalf e := by
  exact PortLookup.get_index _ _ _ _

/-- The equalities at the inserted vertices are exactly wire consistency.
    The remaining constraints are precisely those of the original network. -/
theorem subdivisionSatisfies_iff (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (y : Fin G.subdivision.nE → Bool) :
    G.SubdivisionSatisfies T y ↔
      (∀ e, y (G.leftHalf e) = y (G.rightHalf e)) ∧
      G.Satisfies T (fun e => y (G.leftHalf e)) := by
  constructor
  · intro h
    have heq : ∀ e, y (G.leftHalf e) = y (G.rightHalf e) := by
      intro e
      have hv := h (G.equalityVertex e)
      simpa only [subdivisionTensor_equalityVertex, get_equalityLeftPort,
        get_equalityRightPort, decide_eq_true_eq] using hv
    refine ⟨heq, fun v => ?_⟩
    have hv := h (G.oldVertex v)
    simp only [subdivisionTensor_oldVertex, get_oldPort] at hv
    convert hv using 2
    funext i
    unfold incidentHalf
    split
    · rfl
    · exact heq _
  · rintro ⟨heq, h⟩ v
    have hold : ∀ v : Fin G.nV,
        G.subdivisionTensor T (G.oldVertex v)
          (fun i => y ((G.subdivision.ports (G.oldVertex v)).get i)) = true := by
      intro v
      simp only [subdivisionTensor_oldVertex, get_oldPort]
      convert h v using 2
      funext i
      unfold incidentHalf
      split
      · rfl
      · exact (heq _).symm
    have hnew : ∀ e : Fin G.nE,
        G.subdivisionTensor T (G.equalityVertex e)
          (fun i => y ((G.subdivision.ports (G.equalityVertex e)).get i)) = true := by
      intro e
      simp only [subdivisionTensor_equalityVertex, get_equalityLeftPort,
        get_equalityRightPort, decide_eq_true_eq]
      exact heq e
    exact Fin.addCases hold hnew v

/-- A satisfying assignment on the subdivided graph is forced by its values on
    the first halves. In particular, subdivision introduces no witness freedom. -/
theorem lift_restrict_of_satisfies (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {y : Fin G.subdivision.nE → Bool} (hy : G.SubdivisionSatisfies T y) :
    G.liftAssignment (fun e => y (G.leftHalf e)) = y := by
  have heq := (G.subdivisionSatisfies_iff T y).1 hy |>.1
  funext e
  refine Fin.addCases (fun e => ?_) (fun e => ?_) e
  · exact G.lift_leftHalf _ e
  · change G.liftAssignment _ (G.rightHalf e) = _
    rw [lift_rightHalf]
    exact heq e

@[simp] theorem lift_satisfies_iff (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (x : Fin G.nE → Bool) :
    G.SubdivisionSatisfies T (G.liftAssignment x) ↔ G.Satisfies T x := by
  rw [subdivisionSatisfies_iff]
  simp only [lift_leftHalf, lift_rightHalf, implies_true, true_and]

/-- The original-network parsimony specification, with the same ordered-port
    convention as `DetDLP.IsParsimonious`. -/
def Parsimonious (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop) : Prop :=
  Function.Injective ext ∧ ∀ z,
    (R z → ∃! x, (∀ i, x (ext i) = z i) ∧ G.Satisfies T x) ∧
    (¬R z → ¬∃ x, (∀ i, x (ext i) = z i) ∧ G.Satisfies T x)

/-- Parsimony survives the concrete bipartite subdivision, including the exact
    interface map and the target's canonical increasing-index port order. -/
theorem subdivision_isParsimonious (G : WireGraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop)
    (h : G.Parsimonious T ext R) :
    IsParsimonious G.subdivision (G.subdivisionTensor T) (fun i => G.leftHalf (ext i)) R := by
  refine ⟨?_, fun z => ⟨?_, ?_⟩⟩
  · intro i j hij
    apply h.1
    exact Fin.castAdd_injective _ _ hij
  · intro hz
    obtain ⟨x, hx, hunique⟩ := (h.2 z).1 hz
    refine ⟨G.liftAssignment x, ⟨?_, (G.lift_satisfies_iff T x).2 hx.2⟩, ?_⟩
    · intro i
      rw [lift_leftHalf]
      exact hx.1 i
    · intro y hy
      have hrestrict : (fun e => y (G.leftHalf e)) = x :=
        hunique _ ⟨hy.1, (G.subdivisionSatisfies_iff T y).1 hy.2 |>.2⟩
      calc y = G.liftAssignment (fun e => y (G.leftHalf e)) :=
          (G.lift_restrict_of_satisfies T hy.2).symm
        _ = G.liftAssignment x := congrArg G.liftAssignment hrestrict
  · rintro hz ⟨y, hyext, hysat⟩
    exact (h.2 z).2 hz ⟨fun e => y (G.leftHalf e), hyext,
      (G.subdivisionSatisfies_iff T y).1 hysat |>.2⟩

/-- Forget which half of an original wire was selected. -/
def forgetHalf (G : WireGraph) : Fin G.subdivision.nE → Fin G.nE :=
  Fin.addCases id id

@[simp] theorem forget_leftHalf (G : WireGraph) (e : Fin G.nE) :
    G.forgetHalf (G.leftHalf e) = e := by
  simp only [forgetHalf, leftHalf, Fin.addCases_left, id_eq]

@[simp] theorem forget_rightHalf (G : WireGraph) (e : Fin G.nE) :
    G.forgetHalf (G.rightHalf e) = e := by
  simp only [forgetHalf, rightHalf, Fin.addCases_right, id_eq]

@[simp] theorem forget_incidentHalf (G : WireGraph) (v : Fin G.nV) (e : Fin G.nE) :
    G.forgetHalf (G.incidentHalf v e) = e := by
  unfold incidentHalf
  split <;> simp

theorem incidentHalf_injective (G : WireGraph) (v : Fin G.nV) :
    Function.Injective (G.incidentHalf v) := by
  intro e f h
  have := congrArg G.forgetHalf h
  simpa only [forget_incidentHalf] using this

@[simp] theorem oldVertex_inj (G : WireGraph) (v w : Fin G.nV) :
    G.oldVertex v = G.oldVertex w ↔ v = w := Fin.castAdd_inj

@[simp] theorem equalityVertex_inj (G : WireGraph) (e f : Fin G.nE) :
    G.equalityVertex e = G.equalityVertex f ↔ e = f := by
  simp [equalityVertex, Fin.ext_iff]

@[simp] theorem oldVertex_ne_equalityVertex (G : WireGraph) (v : Fin G.nV)
    (e : Fin G.nE) : G.oldVertex v ≠ G.equalityVertex e := by
  intro h
  have hv := congrArg Fin.val h
  change v.val = G.nV + e.val at hv
  omega

@[simp] theorem equalityVertex_ne_oldVertex (G : WireGraph) (e : Fin G.nE)
    (v : Fin G.nV) : G.equalityVertex e ≠ G.oldVertex v :=
  (G.oldVertex_ne_equalityVertex v e).symm

@[simp] theorem leftHalf_mem_oldPorts (G : WireGraph) (v : Fin G.nV) (e : Fin G.nE) :
    G.leftHalf e ∈ G.subdivision.ports (G.oldVertex v) ↔ (G.endpoints e).1 = v := by
  rw [PortLookup.mem_ports, endpoints_leftHalf]
  exact (or_iff_left (G.equalityVertex_ne_oldVertex e v)).trans (G.oldVertex_inj _ v)

@[simp] theorem rightHalf_mem_oldPorts (G : WireGraph) (v : Fin G.nV) (e : Fin G.nE) :
    G.rightHalf e ∈ G.subdivision.ports (G.oldVertex v) ↔ (G.endpoints e).2 = v := by
  rw [PortLookup.mem_ports, endpoints_rightHalf]
  exact (or_iff_left (G.equalityVertex_ne_oldVertex e v)).trans (G.oldVertex_inj _ v)

theorem incidentHalf_surjective (G : WireGraph) (v : Fin G.nV)
    (f : Fin G.subdivision.nE) (hf : f ∈ G.subdivision.ports (G.oldVertex v)) :
    ∃ e ∈ G.ports v, G.incidentHalf v e = f := by
  have hleft : ∀ e, G.leftHalf e ∈ G.subdivision.ports (G.oldVertex v) →
      ∃ e' ∈ G.ports v, G.incidentHalf v e' = G.leftHalf e := by
    intro e he
    have h := (G.leftHalf_mem_oldPorts v e).1 he
    refine ⟨e, (mem_ports G v e).2 (Or.inl h), ?_⟩
    simp [incidentHalf, h]
  have hright : ∀ e, G.rightHalf e ∈ G.subdivision.ports (G.oldVertex v) →
      ∃ e' ∈ G.ports v, G.incidentHalf v e' = G.rightHalf e := by
    intro e he
    have h := (G.rightHalf_mem_oldPorts v e).1 he
    have hn : (G.endpoints e).1 ≠ v := by
      intro h'
      exact G.loopless e (h'.trans h.symm)
    refine ⟨e, (mem_ports G v e).2 (Or.inr h), ?_⟩
    simp [incidentHalf, hn]
  exact Fin.addCases hleft hright f hf

theorem ports_nodup (G : WireGraph) (v : Fin G.nV) : (G.ports v).Nodup := by
  exact (List.nodup_finRange _).filter _

theorem subdivision_ports_nodup (G : WireGraph) (v : Fin G.subdivision.nV) :
    (G.subdivision.ports v).Nodup := by
  exact (List.nodup_finRange _).filter _

/-- `oldPort` is a permutation of the complete port list, not a projection that
    might silently discard a wire. -/
theorem oldPort_bijective (G : WireGraph) (v : Fin G.nV) :
    Function.Bijective (G.oldPort v) := by
  constructor
  · intro i j hij
    apply (G.ports_nodup v).get_inj_iff.1
    apply G.incidentHalf_injective v
    have h := congrArg (G.subdivision.ports (G.oldVertex v)).get hij
    simpa only [get_oldPort] using h
  · intro j
    obtain ⟨e, he, hhalf⟩ := G.incidentHalf_surjective v
      ((G.subdivision.ports (G.oldVertex v)).get j) (List.get_mem _ _)
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 he
    refine ⟨i, ?_⟩
    apply (G.subdivision_ports_nodup (G.oldVertex v)).get_inj_iff.1
    exact (G.get_oldPort v i).trans ((congrArg (G.incidentHalf v) hi).trans hhalf)

/-- Subdivision preserves the degree of every original vertex exactly. -/
@[simp] theorem subdivision_deg_oldVertex (G : WireGraph) (v : Fin G.nV) :
    G.subdivision.deg (G.oldVertex v) = G.deg v := by
  have h := Fintype.card_congr (Equiv.ofBijective (G.oldPort v) (G.oldPort_bijective v))
  simpa only [Fintype.card_fin] using h.symm

@[simp] theorem leftHalf_inj (G : WireGraph) (e f : Fin G.nE) :
    G.leftHalf e = G.leftHalf f ↔ e = f := Fin.castAdd_inj

@[simp] theorem rightHalf_inj (G : WireGraph) (e f : Fin G.nE) :
    G.rightHalf e = G.rightHalf f ↔ e = f := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change G.nE + e.val = G.nE + f.val at hv
    omega
  · rintro rfl
    rfl

@[simp] theorem leftHalf_ne_rightHalf (G : WireGraph) (e f : Fin G.nE) :
    G.leftHalf e ≠ G.rightHalf f := by
  intro h
  have hv := congrArg Fin.val h
  change e.val = G.nE + f.val at hv
  omega

@[simp] theorem rightHalf_ne_leftHalf (G : WireGraph) (e f : Fin G.nE) :
    G.rightHalf e ≠ G.leftHalf f := (G.leftHalf_ne_rightHalf f e).symm

@[simp] theorem leftHalf_mem_equalityPorts (G : WireGraph) (e f : Fin G.nE) :
    G.leftHalf f ∈ G.subdivision.ports (G.equalityVertex e) ↔ f = e := by
  rw [PortLookup.mem_ports, endpoints_leftHalf]
  exact (or_iff_right (G.oldVertex_ne_equalityVertex _ e)).trans (G.equalityVertex_inj f e)

@[simp] theorem rightHalf_mem_equalityPorts (G : WireGraph) (e f : Fin G.nE) :
    G.rightHalf f ∈ G.subdivision.ports (G.equalityVertex e) ↔ f = e := by
  rw [PortLookup.mem_ports, endpoints_rightHalf]
  exact (or_iff_right (G.oldVertex_ne_equalityVertex _ e)).trans (G.equalityVertex_inj f e)

theorem mem_equalityPorts_iff (G : WireGraph) (e : Fin G.nE)
    (f : Fin G.subdivision.nE) :
    f ∈ G.subdivision.ports (G.equalityVertex e) ↔
      f = G.leftHalf e ∨ f = G.rightHalf e := by
  have hl : ∀ f, G.leftHalf f ∈ G.subdivision.ports (G.equalityVertex e) ↔
      G.leftHalf f = G.leftHalf e ∨ G.leftHalf f = G.rightHalf e := by
    intro f
    rw [leftHalf_mem_equalityPorts]
    exact ((or_iff_left (G.leftHalf_ne_rightHalf f e)).trans (G.leftHalf_inj f e)).symm
  have hr : ∀ f, G.rightHalf f ∈ G.subdivision.ports (G.equalityVertex e) ↔
      G.rightHalf f = G.leftHalf e ∨ G.rightHalf f = G.rightHalf e := by
    intro f
    rw [rightHalf_mem_equalityPorts]
    exact ((or_iff_right (G.rightHalf_ne_leftHalf f e)).trans (G.rightHalf_inj f e)).symm
  exact Fin.addCases hl hr f

/-- Each new equality tensor has exactly two Boolean inputs. -/
@[simp] theorem subdivision_deg_equalityVertex (G : WireGraph) (e : Fin G.nE) :
    G.subdivision.deg (G.equalityVertex e) = 2 := by
  have heq : (G.subdivision.ports (G.equalityVertex e)).toFinset =
      {G.leftHalf e, G.rightHalf e} := by
    ext f
    simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    exact G.mem_equalityPorts_iff e f
  change (G.subdivision.ports (G.equalityVertex e)).length = 2
  rw [← List.toFinset_card_of_nodup (G.subdivision_ports_nodup _), heq]
  exact Finset.card_pair (G.leftHalf_ne_rightHalf e e)

/-- A uniform degree bound is preserved, up to the new degree-two vertices. -/
theorem subdivision_maxDeg_le (G : WireGraph) (D : ℕ)
    (hD : ∀ v, G.deg v ≤ D) : G.subdivision.maxDeg ≤ max D 2 := by
  apply Finset.sup_le
  intro v _
  have hold : ∀ v : Fin G.nV, G.subdivision.deg (G.oldVertex v) ≤ max D 2 := by
    intro v
    rw [subdivision_deg_oldVertex]
    exact (hD v).trans (le_max_left _ _)
  have hnew : ∀ e : Fin G.nE, G.subdivision.deg (G.equalityVertex e) ≤ max D 2 := by
    intro e
    rw [subdivision_deg_equalityVertex]
    exact le_max_right _ _
  exact Fin.addCases hold hnew v

/-- The concrete bipartite conversion doubles the edge budget and preserves
    any degree budget at least two. -/
theorem subdivision_size_bounds (G : WireGraph) (d D : ℕ)
    (hE : 2 * G.nE < 1100 * (d + 1)) (hD : ∀ v, G.deg v ≤ D) (hD2 : 2 ≤ D)
    (hDR : (D : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4)) :
    G.subdivision.nE < 1100 * (d + 1) ∧
    (G.subdivision.maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) := by
  refine ⟨by simpa only [subdivision_nE] using hE, ?_⟩
  have hmax := G.subdivision_maxDeg_le D hD
  rw [max_eq_left hD2] at hmax
  exact (Nat.cast_le.mpr hmax).trans_lt hDR


end WireGraph
end DetDLP.w4_M5Network


