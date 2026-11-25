-- Prove2me | Definitions.Def_DetDLP_W4_M5MixedNetwork
-- name    : DetDLP_W4_M5MixedNetwork
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:33:42.849447+00:00
-- url     : https://prove2.me/theorems/36aff3d2-f9ce-4561-a77b-6717a22c4758
-- title:
--   Boolean expansion of mixed-width wire networks
-- statement:
--   Permits different bit widths for external and internal wires; proves exact preservation of port incidence and parsimony under direct bipartite expansion.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_DetDLP_W4_M5WordNetwork

set_option autoImplicit false

namespace DetDLP.w4_M5Network
namespace WireGraph

/-- Mixed-width wires, with an explicit finite encoding. In the multiplier,
    interface wires have width one and internal residue/carry wires have width
    `J+1`. The encoding argument is kept explicit to permit a computable choice. -/
def mixedExpansion (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) : WireGraph where
  nV := G.nV
  nE := B
  endpoints f := G.endpoints (enc.symm f).1
  loopless f := G.loopless (enc.symm f).1

/-- Every such explicit mixed-width encoding has exactly the sum of the widths. -/
theorem mixedExpansion_nE (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) :
    (G.mixedExpansion width enc).nE = ∑ e, width e := by
  change B = ∑ e, width e
  have h := Fintype.card_congr enc
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h.symm

@[simp] theorem mixedExpansion_endpoints (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) (p : Σ e, Fin (width e)) :
    (G.mixedExpansion width enc).endpoints (enc p) = G.endpoints p.1 := by
  exact congrArg (fun p : Σ e, Fin (width e) => G.endpoints p.1) (enc.symm_apply_apply p)

@[simp] theorem mixedExpansion_mem_ports (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) (v : Fin G.nV) (p : Σ e, Fin (width e)) :
    enc p ∈ (G.mixedExpansion width enc).ports v ↔ p.1 ∈ G.ports v := by
  refine ((G.mixedExpansion width enc).mem_ports v (enc p)).trans ?_
  rw [G.mixedExpansion_endpoints width enc p]
  exact (G.mem_ports v p.1).symm

/-- Port position of an individual bit of a mixed-width incident wire. -/
def mixedPort (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) (v : Fin G.nV)
    (p : Σ e, Fin (width e)) (hp : p.1 ∈ G.ports v) :
    Fin ((G.mixedExpansion width enc).deg v) :=
  (G.mixedExpansion width enc).portIndex v (enc p)
    ((G.mixedExpansion_mem_ports width enc v p).2 hp)

@[simp] theorem get_mixedPort (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) (v : Fin G.nV)
    (p : Σ e, Fin (width e)) (hp : p.1 ∈ G.ports v) :
    ((G.mixedExpansion width enc).ports v).get (G.mixedPort width enc v p hp) = enc p :=
  (G.mixedExpansion width enc).get_portIndex v (enc p) _

/-- The mixed Boolean port list enumerates exactly every bit of every incident
    original wire, once. -/
noncomputable def mixedPortEquiv (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) (v : Fin G.nV) :
    {p : Σ e, Fin (width e) // p.1 ∈ G.ports v} ≃ Fin ((G.mixedExpansion width enc).deg v) :=
  Equiv.ofBijective (fun p => G.mixedPort width enc v p.1 p.2) (by
    constructor
    · intro p q h
      apply Subtype.ext
      apply enc.injective
      have he := congrArg ((G.mixedExpansion width enc).ports v).get h
      exact (G.get_mixedPort width enc v p.1 p.2).symm.trans
        (he.trans (G.get_mixedPort width enc v q.1 q.2))
    · intro j
      let f := ((G.mixedExpansion width enc).ports v).get j
      have hp : (enc.symm f).1 ∈ G.ports v := by
        apply (G.mixedExpansion_mem_ports width enc v (enc.symm f)).1
        exact (enc.apply_symm_apply f).symm ▸ List.get_mem _ j
      refine ⟨⟨enc.symm f, hp⟩, ?_⟩
      apply ((G.mixedExpansion width enc).ports_nodup v).get_inj_iff.1
      exact (G.get_mixedPort width enc v (enc.symm f) hp).trans (enc.apply_symm_apply f))

/-- Split the bit-incidence subtype into an incident-wire subtype and its bit. -/
def mixedIncidenceEquiv (G : WireGraph) (width : Fin G.nE → ℕ) (v : Fin G.nV) :
    {p : Σ e, Fin (width e) // p.1 ∈ G.ports v} ≃
      Σ e : {e : Fin G.nE // e ∈ G.ports v}, Fin (width e.1) where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- Exact degree in mixed-width bit expansion. -/
theorem mixedExpansion_deg (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) (v : Fin G.nV) :
    (G.mixedExpansion width enc).deg v =
      ∑ e : {e : Fin G.nE // e ∈ G.ports v}, width e.1 := by
  have h := Fintype.card_congr
    ((G.mixedPortEquiv width enc v).symm.trans (G.mixedIncidenceEquiv width v))
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

/-- Purely local tensor compiled from mixed-width global checks. -/
def mixedLocalTensor (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B)
    (check : Fin G.nV → ((e : Fin G.nE) → Fin (width e) → Bool) → Bool) :
    (v : Fin (G.mixedExpansion width enc).nV) →
      (Fin ((G.mixedExpansion width enc).deg v) → Bool) → Bool :=
  fun v α => check v (fun e b =>
    if h : e ∈ G.ports v then α (G.mixedPort width enc v ⟨e, b⟩ h) else false)

/-- Locality is the only hypothesis needed to convert a global mixed-word
    checker to a finite ordered-port tensor. -/
theorem mixedLocalTensor_eval (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B)
    (check : Fin G.nV → ((e : Fin G.nE) → Fin (width e) → Bool) → Bool)
    (hloc : ∀ v x y, (∀ e ∈ G.ports v, x e = y e) → check v x = check v y)
    (v : Fin G.nV) (x : Fin B → Bool) :
    G.mixedLocalTensor width enc check v
      (fun i => x (((G.mixedExpansion width enc).ports v).get i)) =
      check v (fun e b => x (enc ⟨e, b⟩)) := by
  apply hloc
  intro e he
  funext b
  dsimp only
  rw [dif_pos he]
  exact congrArg x (G.get_mixedPort width enc v ⟨e, b⟩ he)

/-- A canonical run on mixed-width words yields exact Boolean parsimony. -/
theorem mixedExpansion_parsimonious (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B)
    (check : Fin G.nV → ((e : Fin G.nE) → Fin (width e) → Bool) → Bool)
    (hloc : ∀ v x y, (∀ e ∈ G.ports v, x e = y e) → check v x = check v y)
    {k : ℕ} (ext : Fin k → Σ e, Fin (width e)) (R : (Fin k → Bool) → Prop)
    (hext : Function.Injective ext)
    (run : (Fin k → Bool) → (e : Fin G.nE) → Fin (width e) → Bool)
    (run_ext : ∀ z, R z → ∀ i, run z (ext i).1 (ext i).2 = z i)
    (run_sat : ∀ z, R z → ∀ v, check v (run z) = true)
    (sound : ∀ z x, (∀ i, x (ext i).1 (ext i).2 = z i) →
      (∀ v, check v x = true) → R z)
    (unique : ∀ z x, (∀ i, x (ext i).1 (ext i).2 = z i) →
      (∀ v, check v x = true) → x = run z) :
    (G.mixedExpansion width enc).Parsimonious (G.mixedLocalTensor width enc check)
      (fun i => enc (ext i)) R := by
  have sat_iff : ∀ x : Fin B → Bool,
      (G.mixedExpansion width enc).Satisfies (G.mixedLocalTensor width enc check) x ↔
        ∀ v, check v (fun e b => x (enc ⟨e, b⟩)) = true := by
    intro x
    constructor
    · intro hx v
      exact (G.mixedLocalTensor_eval width enc check hloc v x).symm.trans (hx v)
    · intro hx v
      exact (G.mixedLocalTensor_eval width enc check hloc v x).trans (hx v)
  have cancel : ∀ z, (fun e b => run z (enc.symm (enc ⟨e, b⟩)).1
      (enc.symm (enc ⟨e, b⟩)).2) = run z := by
    intro z
    funext e b
    exact congrArg (fun p : Σ e, Fin (width e) => run z p.1 p.2) (enc.symm_apply_apply ⟨e, b⟩)
  refine ⟨enc.injective.comp hext, fun z => ⟨?_, ?_⟩⟩
  · intro hz
    refine ⟨fun f => run z (enc.symm f).1 (enc.symm f).2, ⟨?_, ?_⟩, ?_⟩
    · intro i
      exact (congrArg (fun p : Σ e, Fin (width e) => run z p.1 p.2)
        (enc.symm_apply_apply (ext i))).trans (run_ext z hz i)
    · apply (sat_iff _).2
      rw [cancel]
      exact run_sat z hz
    · intro y hy
      have heq := unique z (fun e b => y (enc ⟨e, b⟩)) hy.1 ((sat_iff y).1 hy.2)
      funext f
      have hv := congrArg (fun x : (e : Fin G.nE) → Fin (width e) → Bool =>
        x (enc.symm f).1 (enc.symm f).2) heq
      exact (congrArg y (enc.apply_symm_apply f)).symm.trans hv
  · rintro hz ⟨y, hy⟩
    exact hz (sound z (fun e b => y (enc ⟨e, b⟩)) hy.1 ((sat_iff y).1 hy.2))

/-- Mixed-width direct expansion, when the original word graph comes with a
    coloring. No extra equality vertices or edge doubling are introduced. -/
def mixedBipartiteBits (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) (side : Fin G.nV → Bool)
    (hs : ∀ e, side (G.endpoints e).1 ≠ side (G.endpoints e).2) : BipartiteMultigraph where
  nV := G.nV
  nE := B
  endpoints := (G.mixedExpansion width enc).endpoints
  side := side
  bipartite f := hs (enc.symm f).1

/-- Mixed-width exact degree in the direct bipartite graph. -/
theorem mixedBipartiteBits_deg (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) (side : Fin G.nV → Bool)
    (hs : ∀ e, side (G.endpoints e).1 ≠ side (G.endpoints e).2) (v : Fin G.nV) :
    (G.mixedBipartiteBits width enc side hs).deg v =
      ∑ e : {e : Fin G.nE // e ∈ G.ports v}, width e.1 :=
  G.mixedExpansion_deg width enc v

/-- The exact numerical multiplier budgets follow from mixed-width wire counts
    and local weighted-degree bounds, with no implicit expansion overhead. -/
theorem mixedBipartiteBits_size_bounds (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) (side : Fin G.nV → Bool)
    (hs : ∀ e, side (G.endpoints e).1 ≠ side (G.endpoints e).2)
    (d D : ℕ) (hE : (∑ e, width e) < 1100 * (d + 1))
    (hD : ∀ v, (∑ e : {e : Fin G.nE // e ∈ G.ports v}, width e.1) ≤ D)
    (hDR : (D : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4)) :
    (G.mixedBipartiteBits width enc side hs).nV = G.nV ∧
    (G.mixedBipartiteBits width enc side hs).nE < 1100 * (d + 1) ∧
    ((G.mixedBipartiteBits width enc side hs).maxDeg : ℝ) <
      136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) := by
  refine ⟨rfl, ?_, ?_⟩
  · change B < 1100 * (d + 1)
    have heq : B = ∑ e, width e := G.mixedExpansion_nE width enc
    exact heq.symm ▸ hE
  · have hmax : (G.mixedBipartiteBits width enc side hs).maxDeg ≤ D := by
      apply Finset.sup_le
      intro v _
      exact (G.mixedBipartiteBits_deg width enc side hs v) ▸ hD v
    exact (Nat.cast_le.mpr hmax).trans_lt hDR

/-- The complete direct graph/parsimony bridge for the actual mixed-width
    multiplier interface. The remaining hypotheses are exactly locality and the
    canonical-run correctness/uniqueness obligations of the arithmetic network. -/
theorem mixed_checks_to_colored_btn (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B) (side : Fin G.nV → Bool)
    (hs : ∀ e, side (G.endpoints e).1 ≠ side (G.endpoints e).2)
    (check : Fin G.nV → ((e : Fin G.nE) → Fin (width e) → Bool) → Bool)
    (hloc : ∀ v x y, (∀ e ∈ G.ports v, x e = y e) → check v x = check v y)
    {k : ℕ} (ext : Fin k → Σ e, Fin (width e)) (R : (Fin k → Bool) → Prop)
    (hext : Function.Injective ext)
    (run : (Fin k → Bool) → (e : Fin G.nE) → Fin (width e) → Bool)
    (run_ext : ∀ z, R z → ∀ i, run z (ext i).1 (ext i).2 = z i)
    (run_sat : ∀ z, R z → ∀ v, check v (run z) = true)
    (sound : ∀ z x, (∀ i, x (ext i).1 (ext i).2 = z i) →
      (∀ v, check v x = true) → R z)
    (unique : ∀ z x, (∀ i, x (ext i).1 (ext i).2 = z i) →
      (∀ v, check v x = true) → x = run z) :
    IsParsimonious (G.mixedBipartiteBits width enc side hs)
      (G.mixedLocalTensor width enc check) (fun i => enc (ext i)) R :=
  G.mixedExpansion_parsimonious width enc check hloc ext R hext run run_ext run_sat sound unique

/-- Without a supplied coloring the same semantic bridge uses the verified
    subdivision construction; its precise edge cost is twice the width sum. -/
theorem mixed_checks_to_btn (G : WireGraph) (width : Fin G.nE → ℕ) {B : ℕ}
    (enc : (Σ e, Fin (width e)) ≃ Fin B)
    (check : Fin G.nV → ((e : Fin G.nE) → Fin (width e) → Bool) → Bool)
    (hloc : ∀ v x y, (∀ e ∈ G.ports v, x e = y e) → check v x = check v y)
    {k : ℕ} (ext : Fin k → Σ e, Fin (width e)) (R : (Fin k → Bool) → Prop)
    (hext : Function.Injective ext)
    (run : (Fin k → Bool) → (e : Fin G.nE) → Fin (width e) → Bool)
    (run_ext : ∀ z, R z → ∀ i, run z (ext i).1 (ext i).2 = z i)
    (run_sat : ∀ z, R z → ∀ v, check v (run z) = true)
    (sound : ∀ z x, (∀ i, x (ext i).1 (ext i).2 = z i) →
      (∀ v, check v x = true) → R z)
    (unique : ∀ z x, (∀ i, x (ext i).1 (ext i).2 = z i) →
      (∀ v, check v x = true) → x = run z) :
    IsParsimonious (G.mixedExpansion width enc).subdivision
      ((G.mixedExpansion width enc).subdivisionTensor (G.mixedLocalTensor width enc check))
      (fun i => (G.mixedExpansion width enc).leftHalf (enc (ext i))) R :=
  (G.mixedExpansion width enc).subdivision_isParsimonious (G.mixedLocalTensor width enc check) _ R
    (G.mixedExpansion_parsimonious width enc check hloc ext R hext run run_ext run_sat sound unique)

end WireGraph


end DetDLP.w4_M5Network


