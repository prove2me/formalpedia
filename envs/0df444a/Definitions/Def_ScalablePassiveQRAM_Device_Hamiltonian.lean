-- Prove2me | Definitions.Def_ScalablePassiveQRAM_Device_Hamiltonian
-- name    : ScalablePassiveQRAM_Device_Hamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:31:18.814993+00:00
-- url     : https://prove2.me/theorems/916c23d2-b5be-455f-aaab-7d4c46364c0f
-- title:
--   The full physical interaction sum, histories, pinning, and footprints
-- statement:
--   The forward transitions are the exchange, route, and controlled-read operators of the source, lifted to the full tensor product. The two memory-conditioned branches of a leaf read remain one interaction term. The schedule determines the finite family $\mathcal T_j$ and each support.
--
--   $$H=\sum_{j=1}^{L}J_j\sum_{T\in\mathcal T_j}(T+T^\dagger),\qquad J_j=\frac\Omega2\sqrt{j(L-j+1)},\qquad K=H+P.$$
--
--   The pinning operator sums the on-site energies. Intended configurations are computed by an independent classical execution of the schedule; they are not defined by the action of $H$. Footprints include every visited carrier rail and every switch slice on the selected branch. The incident coupling sum and its maximum $\kappa$ are computed from the interaction family.
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), §§3.2–3.4,4.1, equations (19)–(24),(41),(53), pp.15–16,23,27. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Registers
import Mathlib

noncomputable section
open scoped BigOperators Matrix

namespace ScalablePassiveQRAM.Device

structure Transition (n : ℕ) where
  operator : Op (Basis n)
  support : Finset (Qubit n)

def monomial {n : ℕ} (qs : List (Qubit n × Bool)) : Transition n := by
  classical
  exact ⟨(qs.map fun (q,up) => if up then raising q else lowering q).prod,
    (qs.map Prod.fst).toFinset⟩

def exchangeQ (n : ℕ) (p : ℕ → Bool) : ExchangePort → Bool → Option (Qubit n)
  | .address k, b => some (portQ n k b)
  | .bus, b => some (portQ n n b)
  | .switch d r, b => switchQ n d r p b

def nodes (d : ℕ) : List (Address d) := by
  classical
  exact Finset.univ.toList

def flavors (bit : Bool) : List (Fin 3) := if bit then [1,2] else [0]

/-- All physical forward terms of step j, with read Q_{x,c} kept as one summand. -/
def transitions (n j : ℕ) : List (Transition n) := by
  classical
  exact match (schedule n)[j]? with
    | none => []
    | some (.exchange r into d) => (nodes d).flatMap fun v =>
      [false,true].filterMap fun c => (exchangeQ n (bits d v) r c).map fun q =>
        if into then monomial [(carrierQ n (j+1) (bits d v) (bitFlavor c),true),
          (carrierQ n j (bits d v) 0,false), (q,false)]
        else monomial [(carrierQ n (j+1) (bits d v) 0,true),
          (carrierQ n j (bits d v) (bitFlavor c),false), (q,true)]
    | some (.route d down bit) => (nodes d).flatMap fun v =>
      [false,true].flatMap fun c => (flavors bit).filterMap fun s =>
        let p := bits d v
        let child := fun i => if i = d then c else p i
        let r := routeCount n j d
        match switchQ n d r p c, switchQ n d (r+1) p c with
        | some old, some new => some (monomial [
            (carrierQ n (j+1) (if down then child else p) s,true),
            (carrierQ n j (if down then p else child) s,false), (old,false), (new,true)])
        | _,_ => none
    | some .read => (nodes n).flatMap fun x => [false,true].map fun c =>
        let p := bits n x
        let src := lowering (carrierQ n j p (bitFlavor c))
        let m := memoryQ n x
        let a := raising (carrierQ n (j+1) p (bitFlavor c)) * src *
          onQubit m (outer (ket false) (ket false))
        let b := raising (carrierQ n (j+1) p (bitFlavor (!c))) * src *
          onQubit m (outer (ket true) (ket true))
        ⟨a+b, {carrierQ n j p (bitFlavor c), carrierQ n (j+1) p 1,
          carrierQ n (j+1) p 2, m}⟩

/-- Coupling (19); j is zero based here, so the source index is j+1. -/
def coupling (n : ℕ) (Ω : ℝ) (j : ℕ) : ℝ :=
  Ω / 2 * Real.sqrt (((j+1 : ℕ) : ℝ) * ((length n - j : ℕ) : ℝ))

def interaction (n : ℕ) (Ω : ℝ) (j : ℕ) (t : Transition n) : Op (Basis n) :=
  (coupling n Ω j : ℂ) • (t.operator + t.operator.conjTranspose)

/-- Equations (19)–(24), on every physical bit configuration, including invalid unary states. -/
def hamiltonian (n : ℕ) (Ω : ℝ) : Op (Basis n) :=
  ((List.range (length n)).map fun j =>
    ((transitions n j).map (interaction n Ω j)).sum).sum

def pinning (n : ℕ) (Δ : ℝ) : Op (Basis n) := by
  classical
  exact ∑ q, (Δ * pinningWeight q : ℂ) • number q

def physicalHamiltonian (n : ℕ) (Ω Δ : ℝ) : Op (Basis n) :=
  hamiltonian n Ω + pinning n Δ

/-- Schrödinger evolution uses the matrix exponential and the spectral norm convention. -/
def evolve {a : Type} [Fintype a] [DecidableEq a] (H : Op a) (t : ℝ) : Op a :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • H)

def jStar (n : ℕ) (Ω : ℝ) : ℝ :=
  ((List.range (length n)).map (coupling n Ω)).foldl max 0

/-- Incident coupling weight (63), computed from the actual interaction family. -/
def incident (n : ℕ) (Ω : ℝ) (q : Qubit n) : ℝ := by
  classical
  exact ((List.range (length n)).map fun j =>
    ((transitions n j).filter (fun t => decide (q ∈ t.support))).length * coupling n Ω j).sum

def kappa (n : ℕ) (Ω : ℝ) : ℝ := by
  classical
  exact (Finset.univ.toList.map fun (q : Auxiliary n) =>
    incident n Ω (.inr (.inl q))).foldl max 0

/-- Explicit classical execution, independent of the Hamiltonian's action. -/
def advance (n j : ℕ) (x : Address n) (b : Bool) (D : Database n)
    (state : Fin 3 × Basis n) : Fin 3 × Basis n := by
  classical
  let p := bits n x
  let old := carrierQ n j p state.1
  let base := Function.update state.2 old false
  exact match (schedule n)[j]? with
  | none => state
  | some (.exchange r into _) =>
    let c := match r with
      | .address k => bits n x k
      | .bus => b
      | .switch d _ => bits n x d
    let s := if into then bitFlavor c else 0
    let updated := match exchangeQ n p r (if into then c else state.1 == 2) with
      | none => base
      | some q => Function.update base q (!into)
    (s, Function.update updated (carrierQ n (j+1) p s) true)
  | some (.route d _ _) =>
    let r := routeCount n j d
    let updated := match switchQ n d r p (bits n x d), switchQ n d (r+1) p (bits n x d) with
      | some old, some new => Function.update (Function.update base old false) new true
      | _,_ => base
    (state.1, Function.update updated (carrierQ n (j+1) p state.1) true)
  | some .read =>
    let s := bitFlavor (xor (state.1 == 2) (D x))
    (s, Function.update base (carrierQ n (j+1) p s) true)

def historyConfig (n j : ℕ) (x : Address n) (b : Bool) (D : Database n) : Basis n :=
  (((List.range j).foldl (fun state k => advance n k x b D state)
    (0,endpoint n 0 x b D))).2

def history (n j : ℕ) (x : Address n) (b : Bool) (D : Database n) : Vector (Basis n) := by
  classical
  exact ket (historyConfig n j x b D)

/-- The footprint is constructed from every visited carrier and switch slice. -/
def footprint (n : ℕ) (x : Address n) : Finset (Qubit n) := by
  classical
  exact Finset.univ.filter fun q => match q with
    | .inr (.inl (.inl ⟨j,v,_⟩)) => v = fun i => bits n x i.val
    | .inr (.inl (.inr ⟨d,v,_,_⟩)) => v = fun i => bits n x i.val
    | _ => false

def footprintSize (n : ℕ) : ℕ := 10*n^2 + 14*n + 12

end ScalablePassiveQRAM.Device


