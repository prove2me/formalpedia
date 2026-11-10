-- Prove2me | Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing
-- name    : FasterDistributedMatching_ApproximateMatching_Routing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:13:16.624004+00:00
-- url     : https://prove2.me/theorems/966800c3-aa28-4473-8f6a-454a4f2a1806
-- title:
--   Line-graph colors and operational physical simulation interfaces
-- statement:
--   The line graph has one vertex per physical edge, with adjacency for shared endpoints. A graph power joins distinct vertices connected by a walk of length at most its exponent. A copy receives the color of an assigned incident edge together with the endpoint bit ordered by identifiers. Assigned edges differ among copies at the same creator.
--
--   $$\text{physical rounds}\le C(r+1)\,\text{auxiliary rounds}$$
--
--   is the routed simulation specification: a single physical protocol must reproduce every supplied auxiliary protocol on every finite placement with specified physical routes of length at most $r$. Inputs give each processor only its own hosted auxiliary records and incident route lists. A separate line-graph-power simulation uses only physical neighbors and hosted incident-edge records, with no supplied remote routes or neighborhoods; it allows a setup cost of $O(r+1)$. Edge processors are hosted at the endpoint of smaller identifier. These specifications quantify over actual executions; no simulator is supplied with a correctness certificate.
--
--   The interfaces distinguish auxiliary distances from charged physical communication and retain unique routing identities even when colors repeat.
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Lemma 3.3, printed p.9, PDF p.11; §3.2, printed pp.11–12, PDF pp.13–14; Appendix A, printed p.22, PDF p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Pairwise

namespace FasterDistributedMatching.ApproximateMatching

/-! §3.2 and Appendix A: line-graph power, copy colors, and specified physical routes.
This is routing data, not a certificate that a simulation algorithm works. -/
def lineGraph {N : ℕ} (G : SimpleGraph (Fin N)) : SimpleGraph G.edgeSet where
  Adj e f := e ≠ f ∧ ∃ v : Fin N, v ∈ (e : Sym2 (Fin N)) ∧ v ∈ (f : Sym2 (Fin N))
  symm := ⟨by intro e f h; obtain ⟨v,hv,hv'⟩ := h.2; exact ⟨h.1.symm,v,hv',hv⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

def graphPower {V : Type} (H : SimpleGraph V) (r : ℕ) : SimpleGraph V where
  Adj a b := a ≠ b ∧ Close H r a b
  symm := ⟨by intro a b h; obtain ⟨w,hw⟩ := h.2; exact ⟨h.1.symm,w.reverse,by simpa using hw⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

def Proper {V : Type} (H : SimpleGraph V) (zeta : ℕ) (col : V → ℕ) : Prop :=
  (∀ a, col a < zeta) ∧ ∀ a b, H.Adj a b → col a ≠ col b

/- Assign an incident physical edge of each copy's creator; distinct copies at the same
creator get distinct edges. No global injectivity of assigned edges is intended. -/
def CopyEdgeChoice {N : ℕ} (G : SimpleGraph (Fin N)) (p : Pairing N) (pick : Copy p → Fin N) : Prop :=
  (∀ a, G.Adj a.1 (pick a)) ∧
    ∀ a b, a.1 = b.1 → a ≠ b → pick a ≠ pick b

open Classical in
noncomputable def copyColor {N : ℕ} {p : Pairing N} (ids : Fin N → ℕ)
    (chi : Sym2 (Fin N) → ℕ) (pick : Copy p → Fin N) (a : Copy p) : ℕ :=
  2 * chi s(a.1,pick a) + if ids a.1 < ids (pick a) then 0 else 1

/- Routes exist only for adjacent auxiliary nodes. Each auxiliary node has its own
routing identity even when several are hosted by the same physical processor. -/
structure Routed {N : ℕ} (G : SimpleGraph (Fin N)) (V : Type) where
  graph : SimpleGraph V
  owner : V → Fin N
  identity : V → ℕ
  identity_injective : Function.Injective identity
  route : ∀ a b, graph.Adj a b → G.Walk (owner a) (owner b)

def RouteLength {N : ℕ} {G : SimpleGraph (Fin N)} {V : Type}
    (D : Routed G V) (r : ℕ) : Prop := ∀ a b h, (D.route a b h).length ≤ r

abbrev RouteInput (I : Type) := Finset (ℕ × I × Finset (ℕ × List ℕ))

/- Exactly the locally hosted auxiliary states and their incident route lists.
Intermediate processors need no remote auxiliary topology as initial input. -/
open Classical in
noncomputable def routeInput {N : ℕ} {G : SimpleGraph (Fin N)} {V I : Type}
    [Fintype V] (D : Routed G V) (ids : Fin N → ℕ) (inp : V → I) (v : Fin N) :
    Finset ℕ × RouteInput I :=
  (neighborIDs G ids v,
    (Finset.univ.filter (fun a => D.owner a = v)).image fun a =>
      (D.identity a, inp a,
        (Finset.univ.filter (D.graph.Adj a)).attach.image fun b =>
          (D.identity b.val, ((D.route a b.val (Finset.mem_filter.mp b.property).2).support.map ids))))

/- Line-graph processors are hosted at the incident endpoint of smaller ID. The
input contains only that endpoint's actual incident edge records and physical neighbors. -/
def HostsEdge {N : ℕ} (ids : Fin N → ℕ) (e : Sym2 (Fin N)) (v : Fin N) : Prop :=
  v ∈ e ∧ ∀ w ∈ e, ids v ≤ ids w

noncomputable def edgeIdentity {N : ℕ} (ids : Fin N → ℕ) : Sym2 (Fin N) → ℕ :=
  Sym2.lift ⟨(fun u v => Nat.pair (min (ids u) (ids v)) (max (ids u) (ids v))),
    by intro u v; simp only [min_comm, max_comm]⟩

open Classical in
noncomputable def lineInput {N : ℕ} (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    {I : Type} (inp : G.edgeSet → I) (v : Fin N) : Finset ℕ × Finset (ℕ × I) :=
  (neighborIDs G ids v,
    (Finset.univ.filter (fun e : G.edgeSet => HostsEdge ids e.val v)).image
      (fun e => (edgeIdentity ids e.val, inp e)))

/- Operational simulation of the line-graph power without supplied remote routes,
auxiliary neighborhoods or a copy of the physical graph in initial input. -/
open Classical in
noncomputable def LineSimulation : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (K I O : Type) (A : Deterministic K I O),
    ∃ S : Deterministic (K × ℕ) (Finset ℕ × Finset (ℕ × I)) (ℕ → Option O),
      (∀ k r, S.program.rounds (k,r) ≤ C * (r + 2) * (A.program.rounds k + 1)) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ),
        Function.Injective ids → ∀ k r (inp : G.edgeSet → I) (e : G.edgeSet) v,
          HostsEdge ids e.val v →
          execute S G (k,r) ids (lineInput G ids inp) v (edgeIdentity ids e.val) =
            some (A.program.output (graphPower (lineGraph G) r) k
              (fun f => edgeIdentity ids f.val) inp (fun _ _ => false) e)

/- Universal operational emulation: the physical program is fixed before any graph,
placement, route, IDs or inputs. Its time is charged in physical rounds. -/
def RoutedSimulation : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (K I O : Type) (A : Deterministic K I O),
    ∃ S : Deterministic (K × ℕ) (Finset ℕ × RouteInput I) (ℕ → Option O),
      (∀ k r, S.program.rounds (k,r) ≤ C * (r + 1) * A.program.rounds k) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (V : Type) [Fintype V]
        (D : Routed G V) (r : ℕ), RouteLength D r →
        ∀ ids : Fin N → ℕ, Function.Injective ids → ∀ k (inp : V → I) a,
          execute S G (k,r) ids (routeInput D ids inp) (D.owner a) (D.identity a) =
            some (A.program.output D.graph k D.identity inp (fun _ _ => false) a)

end FasterDistributedMatching.ApproximateMatching


