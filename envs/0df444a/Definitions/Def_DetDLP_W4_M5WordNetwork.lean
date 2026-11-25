-- Prove2me | Definitions.Def_DetDLP_W4_M5WordNetwork
-- name    : DetDLP_W4_M5WordNetwork
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:32:09.184911+00:00
-- url     : https://prove2.me/theorems/ebb6171f-8e03-4a56-9b67-921149d74dfa
-- title:
--   Boolean expansion of fixed-width wire networks
-- statement:
--   Expands word wires into individual bits and transports local checks, parsimony and degree bounds to Boolean tensors.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_DetDLP_W4_M5Subdivision

set_option autoImplicit false

namespace DetDLP.w4_M5Network
namespace WireGraph

/-- Boolean expansion of a network whose wires carry `W` bits. -/
def bitExpansion (G : WireGraph) (W : ℕ) : WireGraph where
  nV := G.nV
  nE := G.nE * W
  endpoints f := G.endpoints (finProdFinEquiv.symm f).1
  loopless f := G.loopless (finProdFinEquiv.symm f).1

def bitEdge (G : WireGraph) (W : ℕ) (e : Fin G.nE) (b : Fin W) :
    Fin (G.bitExpansion W).nE := finProdFinEquiv (e, b)

@[simp] theorem bitExpansion_nV (G : WireGraph) (W : ℕ) :
    (G.bitExpansion W).nV = G.nV := rfl

@[simp] theorem bitExpansion_nE (G : WireGraph) (W : ℕ) :
    (G.bitExpansion W).nE = G.nE * W := rfl

@[simp] theorem endpoints_bitEdge (G : WireGraph) (W : ℕ) (e : Fin G.nE) (b : Fin W) :
    (G.bitExpansion W).endpoints (G.bitEdge W e b) = G.endpoints e := by
  exact congrArg (fun p : Fin G.nE × Fin W => G.endpoints p.1)
    (finProdFinEquiv.symm_apply_apply (e, b))

@[simp] theorem bitEdge_mem_ports (G : WireGraph) (W : ℕ) (v : Fin G.nV)
    (e : Fin G.nE) (b : Fin W) :
    G.bitEdge W e b ∈ (G.bitExpansion W).ports v ↔ e ∈ G.ports v := by
  refine ((G.bitExpansion W).mem_ports v (G.bitEdge W e b)).trans ?_
  rw [G.endpoints_bitEdge W e b]
  exact (G.mem_ports v e).symm

/-- Position of one bit of one original port in the expanded Boolean port list. -/
def bitPort (G : WireGraph) (W : ℕ) (v : Fin G.nV) (i : Fin (G.deg v)) (b : Fin W) :
    Fin ((G.bitExpansion W).deg v) :=
  ⟨((G.bitExpansion W).ports v).idxOf (G.bitEdge W ((G.ports v).get i) b),
    List.idxOf_lt_length_of_mem ((G.bitEdge_mem_ports W v _ b).2 (List.get_mem _ _))⟩

@[simp] theorem get_bitPort (G : WireGraph) (W : ℕ) (v : Fin G.nV)
    (i : Fin (G.deg v)) (b : Fin W) :
    ((G.bitExpansion W).ports v).get (G.bitPort W v i b) =
      G.bitEdge W ((G.ports v).get i) b := List.idxOf_get _

theorem bitPort_bijective (G : WireGraph) (W : ℕ) (v : Fin G.nV) :
    Function.Bijective (fun p : Fin (G.deg v) × Fin W => G.bitPort W v p.1 p.2) := by
  constructor
  · rintro ⟨i, b⟩ ⟨j, c⟩ h
    have he := congrArg ((G.bitExpansion W).ports v).get h
    have he' : G.bitEdge W ((G.ports v).get i) b = G.bitEdge W ((G.ports v).get j) c :=
      (G.get_bitPort W v i b).symm.trans (he.trans (G.get_bitPort W v j c))
    have hp := finProdFinEquiv.injective he'
    have hi := (G.ports_nodup v).get_inj_iff.1 (congrArg Prod.fst hp)
    have hb : b = c := congrArg (fun p : Fin G.nE × Fin W => p.2) hp
    exact Prod.ext hi hb
  · intro j
    let f := ((G.bitExpansion W).ports v).get j
    let p : Fin G.nE × Fin W := finProdFinEquiv.symm f
    have hp : G.bitEdge W p.1 p.2 = f := finProdFinEquiv.apply_symm_apply f
    have he : p.1 ∈ G.ports v := (G.bitEdge_mem_ports W v p.1 p.2).1
      (hp.symm ▸ List.get_mem _ j)
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 he
    refine ⟨(i, p.2), ?_⟩
    apply ((G.bitExpansion W).ports_nodup v).get_inj_iff.1
    exact (G.get_bitPort W v i p.2).trans
      ((congrArg (fun e => G.bitEdge W e p.2) hi).trans hp)

/-- Boolean expansion multiplies each vertex degree by the label width exactly. -/
@[simp] theorem bitExpansion_deg (G : WireGraph) (W : ℕ) (v : Fin G.nV) :
    (G.bitExpansion W).deg v = G.deg v * W := by
  have h := Fintype.card_congr (Equiv.ofBijective
    (fun p : Fin (G.deg v) × Fin W => G.bitPort W v p.1 p.2) (G.bitPort_bijective W v))
  simpa only [Fintype.card_prod, Fintype.card_fin] using h.symm

/-- A word tensor is converted by reading exactly one complete Boolean port block
    per original wire. -/
def bitTensor (G : WireGraph) (W : ℕ)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Fin W → Bool) → Bool) :
    (v : Fin (G.bitExpansion W).nV) → (Fin ((G.bitExpansion W).deg v) → Bool) → Bool :=
  fun v α => T v (fun i b => α (G.bitPort W v i b))

def flattenAssignment (G : WireGraph) (W : ℕ) (x : Fin G.nE → Fin W → Bool) :
    Fin (G.bitExpansion W).nE → Bool :=
  fun f => x (finProdFinEquiv.symm f).1 (finProdFinEquiv.symm f).2

def unflattenAssignment (G : WireGraph) (W : ℕ) (y : Fin (G.bitExpansion W).nE → Bool) :
    Fin G.nE → Fin W → Bool := fun e b => y (G.bitEdge W e b)

@[simp] theorem flatten_bitEdge (G : WireGraph) (W : ℕ)
    (x : Fin G.nE → Fin W → Bool) (e : Fin G.nE) (b : Fin W) :
    G.flattenAssignment W x (G.bitEdge W e b) = x e b := by
  exact congrArg (fun p : Fin G.nE × Fin W => x p.1 p.2)
    (finProdFinEquiv.symm_apply_apply (e, b))

@[simp] theorem flatten_unflatten (G : WireGraph) (W : ℕ)
    (y : Fin (G.bitExpansion W).nE → Bool) :
    G.flattenAssignment W (G.unflattenAssignment W y) = y := by
  funext f
  exact congrArg y (finProdFinEquiv.apply_symm_apply f)

@[simp] theorem unflatten_flatten (G : WireGraph) (W : ℕ)
    (x : Fin G.nE → Fin W → Bool) :
    G.unflattenAssignment W (G.flattenAssignment W x) = x := by
  funext e b
  exact G.flatten_bitEdge W x e b

def WordSatisfies (G : WireGraph) (W : ℕ)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Fin W → Bool) → Bool)
    (x : Fin G.nE → Fin W → Bool) : Prop :=
  ∀ v, T v (fun i => x ((G.ports v).get i)) = true

/-- No value or constraint changes when word labels are expanded into bit wires. -/
theorem bitExpansion_satisfies_iff (G : WireGraph) (W : ℕ)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Fin W → Bool) → Bool)
    (y : Fin (G.bitExpansion W).nE → Bool) :
    (G.bitExpansion W).Satisfies (G.bitTensor W T) y ↔
      G.WordSatisfies W T (G.unflattenAssignment W y) := by
  have hloc : ∀ v : Fin G.nV,
      G.bitTensor W T v (fun i => y (((G.bitExpansion W).ports v).get i)) =
        T v (fun i => G.unflattenAssignment W y ((G.ports v).get i)) := by
    intro v
    apply congrArg (T v)
    funext i b
    exact congrArg y (G.get_bitPort W v i b)
  constructor
  · intro h v
    exact (hloc v).symm.trans (h v)
  · intro h v
    exact (hloc v).trans (h v)

/-- Word-network parsimony with an arbitrary collection of exposed individual
    bits, so unpadded input and output widths need not be multiples of `W`. -/
def WordParsimonious (G : WireGraph) (W : ℕ)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Fin W → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE × Fin W) (R : (Fin k → Bool) → Prop) : Prop :=
  Function.Injective ext ∧ ∀ z,
    (R z → ∃! x, (∀ i, x (ext i).1 (ext i).2 = z i) ∧ G.WordSatisfies W T x) ∧
    (¬R z → ¬∃ x, (∀ i, x (ext i).1 (ext i).2 = z i) ∧ G.WordSatisfies W T x)

/-- Bit expansion preserves unique extensions at the individual-bit interface. -/
theorem bitExpansion_parsimonious (G : WireGraph) (W : ℕ)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Fin W → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE × Fin W) (R : (Fin k → Bool) → Prop)
    (h : G.WordParsimonious W T ext R) :
    (G.bitExpansion W).Parsimonious (G.bitTensor W T)
      (fun i => G.bitEdge W (ext i).1 (ext i).2) R := by
  refine ⟨?_, fun z => ⟨?_, ?_⟩⟩
  · intro i j hij
    exact h.1 (finProdFinEquiv.injective hij)
  · intro hz
    obtain ⟨x, hx, hu⟩ := (h.2 z).1 hz
    refine ⟨G.flattenAssignment W x, ⟨?_, ?_⟩, ?_⟩
    · intro i
      rw [flatten_bitEdge]
      exact hx.1 i
    · rw [bitExpansion_satisfies_iff, unflatten_flatten]
      exact hx.2
    · intro y hy
      have heq : G.unflattenAssignment W y = x :=
        hu _ ⟨hy.1, (G.bitExpansion_satisfies_iff W T y).1 hy.2⟩
      calc y = G.flattenAssignment W (G.unflattenAssignment W y) :=
          (G.flatten_unflatten W y).symm
        _ = G.flattenAssignment W x := congrArg (G.flattenAssignment W) heq
  · rintro hz ⟨y, hyext, hysat⟩
    exact (h.2 z).2 hz ⟨G.unflattenAssignment W y, hyext,
      (G.bitExpansion_satisfies_iff W T y).1 hysat⟩

/-- The full word-to-Boolean-to-bipartite semantic bridge. -/
theorem word_to_btn_parsimonious (G : WireGraph) (W : ℕ)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Fin W → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE × Fin W) (R : (Fin k → Bool) → Prop)
    (h : G.WordParsimonious W T ext R) :
    IsParsimonious (G.bitExpansion W).subdivision
      ((G.bitExpansion W).subdivisionTensor (G.bitTensor W T))
      (fun i => (G.bitExpansion W).leftHalf (G.bitEdge W (ext i).1 (ext i).2)) R :=
  (G.bitExpansion W).subdivision_isParsimonious (G.bitTensor W T) _ R
    (G.bitExpansion_parsimonious W T ext R h)

/-- Resource accounting for the full conversion, with no hidden port, equality,
    or bit-expansion factor. -/
theorem word_to_btn_size_bounds (G : WireGraph) (W d D : ℕ)
    (hE : 2 * (G.nE * W) < 1100 * (d + 1))
    (hD : ∀ v, G.deg v * W ≤ D) (hD2 : 2 ≤ D)
    (hDR : (D : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4)) :
    (G.bitExpansion W).subdivision.nV = G.nV + G.nE * W ∧
    (G.bitExpansion W).subdivision.nE = 2 * (G.nE * W) ∧
    (G.bitExpansion W).subdivision.nE < 1100 * (d + 1) ∧
    ((G.bitExpansion W).subdivision.maxDeg : ℝ) <
      136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) := by
  refine ⟨rfl, (G.bitExpansion W).subdivision_nE, ?_⟩
  apply (G.bitExpansion W).subdivision_size_bounds d D hE _ hD2 hDR
  intro v
  exact (G.bitExpansion_deg W v) ▸ hD v

/-- If the word network already has a bipartition, subdivision is unnecessary. -/
def bipartiteBits (G : WireGraph) (W : ℕ) (side : Fin G.nV → Bool)
    (hs : ∀ e, side (G.endpoints e).1 ≠ side (G.endpoints e).2) : BipartiteMultigraph where
  nV := G.nV
  nE := G.nE * W
  endpoints := (G.bitExpansion W).endpoints
  side := side
  bipartite f := hs (finProdFinEquiv.symm f).1

/-- Direct preservation of parsimony when the word-network coloring is supplied.
    This version uses exactly `G.nE * W` Boolean edges. -/
theorem word_to_bipartiteBits_parsimonious (G : WireGraph) (W : ℕ)
    (side : Fin G.nV → Bool)
    (hs : ∀ e, side (G.endpoints e).1 ≠ side (G.endpoints e).2)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Fin W → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE × Fin W) (R : (Fin k → Bool) → Prop)
    (h : G.WordParsimonious W T ext R) :
    IsParsimonious (G.bipartiteBits W side hs) (G.bitTensor W T)
      (fun i => G.bitEdge W (ext i).1 (ext i).2) R :=
  G.bitExpansion_parsimonious W T ext R h

/-- Exact degree preservation for direct Boolean expansion of a bipartite
    word network. -/
theorem bipartiteBits_deg (G : WireGraph) (W : ℕ) (side : Fin G.nV → Bool)
    (hs : ∀ e, side (G.endpoints e).1 ≠ side (G.endpoints e).2) (v : Fin G.nV) :
    (G.bipartiteBits W side hs).deg v = G.deg v * W :=
  G.bitExpansion_deg W v

theorem bipartiteBits_maxDeg_le (G : WireGraph) (W D : ℕ) (side : Fin G.nV → Bool)
    (hs : ∀ e, side (G.endpoints e).1 ≠ side (G.endpoints e).2)
    (hD : ∀ v, G.deg v * W ≤ D) : (G.bipartiteBits W side hs).maxDeg ≤ D := by
  apply Finset.sup_le
  intro v _
  exact (G.bipartiteBits_deg W side hs v) ▸ hD v

/-- Canonical-witness criterion used by functional arithmetic networks.
    It separates the local determinism proof from the port and graph bookkeeping. -/
theorem wordParsimonious_of_canonical (G : WireGraph) (W : ℕ)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Fin W → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE × Fin W) (R : (Fin k → Bool) → Prop)
    (hext : Function.Injective ext)
    (run : (Fin k → Bool) → Fin G.nE → Fin W → Bool)
    (run_ext : ∀ z, R z → ∀ i, run z (ext i).1 (ext i).2 = z i)
    (run_sat : ∀ z, R z → G.WordSatisfies W T (run z))
    (sound : ∀ z x, (∀ i, x (ext i).1 (ext i).2 = z i) →
      G.WordSatisfies W T x → R z)
    (unique : ∀ z x, (∀ i, x (ext i).1 (ext i).2 = z i) →
      G.WordSatisfies W T x → x = run z) : G.WordParsimonious W T ext R := by
  refine ⟨hext, fun z => ⟨?_, ?_⟩⟩
  · intro hz
    exact ⟨run z, ⟨run_ext z hz, run_sat z hz⟩,
      fun x hx => unique z x hx.1 hx.2⟩
  · rintro hn ⟨x, he, hs⟩
    exact hn (sound z x he hs)

/-- Read a wire through the original graph's ordered local-port list. -/
def portIndex (G : WireGraph) (v : Fin G.nV) (e : Fin G.nE) (h : e ∈ G.ports v) :
    Fin (G.deg v) := ⟨(G.ports v).idxOf e, List.idxOf_lt_length_of_mem h⟩

@[simp] theorem get_portIndex (G : WireGraph) (v : Fin G.nV) (e : Fin G.nE)
    (h : e ∈ G.ports v) : (G.ports v).get (G.portIndex v e h) = e := List.idxOf_get _

/-- Complete local input by a fixed zero word outside this vertex's incidence
    set. Locality will ensure the chosen outside values do not matter. -/
def completeLocalWord (G : WireGraph) (W : ℕ) (v : Fin G.nV)
    (α : Fin (G.deg v) → Fin W → Bool) : Fin G.nE → Fin W → Bool :=
  fun e => if h : e ∈ G.ports v then α (G.portIndex v e h) else fun _ => false

theorem completeLocalWord_reads (G : WireGraph) (W : ℕ) (v : Fin G.nV)
    (x : Fin G.nE → Fin W → Bool) (e : Fin G.nE) (he : e ∈ G.ports v) :
    G.completeLocalWord W v (fun i => x ((G.ports v).get i)) e = x e := by
  unfold completeLocalWord
  rw [dif_pos he]
  exact congrArg x (G.get_portIndex v e he)

/-- A global-assignment check is local if it reads only incident wires. This is
    the exact semantic interface of `MulNetDefs.chk_agree`/`mulT_local`. -/
def WordLocal (G : WireGraph) (W : ℕ)
    (check : Fin G.nV → (Fin G.nE → Fin W → Bool) → Bool) : Prop :=
  ∀ v x y, (∀ e ∈ G.ports v, x e = y e) → check v x = check v y

def localWordTensor (G : WireGraph) (W : ℕ)
    (check : Fin G.nV → (Fin G.nE → Fin W → Bool) → Bool) :
    (v : Fin G.nV) → (Fin (G.deg v) → Fin W → Bool) → Bool :=
  fun v α => check v (G.completeLocalWord W v α)

/-- Global checks become tensors on the target's actual finite ordered ports,
    without asking the imported proof to use the same port order. -/
theorem localWordTensor_eval (G : WireGraph) (W : ℕ)
    (check : Fin G.nV → (Fin G.nE → Fin W → Bool) → Bool)
    (hloc : G.WordLocal W check) (v : Fin G.nV) (x : Fin G.nE → Fin W → Bool) :
    G.localWordTensor W check v (fun i => x ((G.ports v).get i)) = check v x :=
  hloc v _ x (fun e he => G.completeLocalWord_reads W v x e he)

theorem localWordTensor_satisfies_iff (G : WireGraph) (W : ℕ)
    (check : Fin G.nV → (Fin G.nE → Fin W → Bool) → Bool)
    (hloc : G.WordLocal W check) (x : Fin G.nE → Fin W → Bool) :
    G.WordSatisfies W (G.localWordTensor W check) x ↔ ∀ v, check v x = true := by
  unfold WordSatisfies
  simp only [G.localWordTensor_eval W check hloc]

/-- A canonical-run proof for global local checks can be transported directly
    to a concrete Boolean bipartite tensor network. -/
theorem local_checks_to_btn (G : WireGraph) (W : ℕ)
    (check : Fin G.nV → (Fin G.nE → Fin W → Bool) → Bool)
    (hloc : G.WordLocal W check)
    {k : ℕ} (ext : Fin k → Fin G.nE × Fin W) (R : (Fin k → Bool) → Prop)
    (hext : Function.Injective ext)
    (run : (Fin k → Bool) → Fin G.nE → Fin W → Bool)
    (run_ext : ∀ z, R z → ∀ i, run z (ext i).1 (ext i).2 = z i)
    (run_sat : ∀ z, R z → ∀ v, check v (run z) = true)
    (sound : ∀ z x, (∀ i, x (ext i).1 (ext i).2 = z i) →
      (∀ v, check v x = true) → R z)
    (unique : ∀ z x, (∀ i, x (ext i).1 (ext i).2 = z i) →
      (∀ v, check v x = true) → x = run z) :
    IsParsimonious (G.bitExpansion W).subdivision
      ((G.bitExpansion W).subdivisionTensor (G.bitTensor W (G.localWordTensor W check)))
      (fun i => (G.bitExpansion W).leftHalf (G.bitEdge W (ext i).1 (ext i).2)) R := by
  apply G.word_to_btn_parsimonious W (G.localWordTensor W check) ext R
  apply G.wordParsimonious_of_canonical W (G.localWordTensor W check) ext R
    hext run run_ext
  · intro z hz
    exact (G.localWordTensor_satisfies_iff W check hloc _).2 (run_sat z hz)
  · intro z x he hs
    exact sound z x he ((G.localWordTensor_satisfies_iff W check hloc x).1 hs)
  · intro z x he hs
    exact unique z x he ((G.localWordTensor_satisfies_iff W check hloc x).1 hs)


end WireGraph
end DetDLP.w4_M5Network


