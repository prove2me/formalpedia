-- Prove2me | Definitions.Def_LowTempGlauber_Supplement_Lifted
-- name    : LowTempGlauber_Supplement_Lifted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:28:06.26439+00:00
-- url     : https://prove2.me/theorems/58e2af81-7253-42a3-be38-b9568044636f
-- title:
--   Lifted random-cluster configurations $\Omega$, the laws $\hat\pi^\pm$, and the events $A_{G,R}$, $B_{G,\ell,r}$, $H^\pm_\theta$
-- statement:
--   Let $G=(V,E)$ be a $d$-regular graph on $n$ vertices, $\beta>0$, $q>2$. A **lifted configuration** is a pair $\omega=(F,S)$ with $F\subseteq E$ and $S\subseteq V$ that is **compatible**: every edge of $F$ has both endpoints in $S$ or both in $V\setminus S$, i.e. $S$ is a union of components of $(V,F)$. Write $\Omega$ for the compatible pairs, $\omega_{\rm edge}=F$, $\omega_{\rm ver}=S$ (the active vertices), $\omega_{\rm inact}$ for the edges of $F$ with both ends in $V\setminus S$, and $\kappa_0(\omega)$ for the number of components of $(V\setminus S,\omega_{\rm inact})$. The lifted law is
--   $$\hat\pi(\omega)\propto(e^\beta-1)^{|\omega_{\rm edge}|}(q-1)^{\kappa_0(\omega)}\qquad(\omega\in\Omega).$$
--   With $\Omega^\pm=\{(F,S)\in\Omega: F\in E^\pm_G\}$, let $\hat\pi^-=\hat\pi(\cdot\mid\Omega^-)$ and
--   $$\hat\pi^+(\omega)=q\,\hat\pi(\omega\mid\Omega^+)\,\mathbf 1\{C_1(\omega)\subseteq S\},$$
--   where $C_1(\omega)$ is a largest component of $(V,F)$.
--
--   For $\omega=(F,S)$, $\omega'=(F',S')$ let $D=S\oplus S'$ and let $H(\omega,\omega')$ be the subgraph of $(V,F\cup F')$ induced by $D$. With $\mathrm{exc}(C)=|E(C)|-|V(C)|+1$ and the total tree excess of a graph equal to $|E|-|V|+\#\text{components}$:
--   1. $A_{G,R}$: one of $(V,\omega_{\rm inact})$, $(V,\omega'_{\rm inact})$ has total tree excess $>R$;
--   2. $B_{G,\ell,r}$: some component $C$ of $H(\omega,\omega')$ has $|V(C)|>\ell$ or $\mathrm{exc}(C)>r$;
--   3. $H^+_\theta$: $\omega,\omega'\in\Omega^+$ and $|\omega_{\rm edge}|\le n(p_c+3\theta)$ or $|\omega'_{\rm edge}|\le n(p_c+3\theta)$;
--   4. $H^-_\theta$: $\omega,\omega'\in\Omega^-$ and $|\omega_{\rm edge}|\ge n(p_c-3\theta)$ or $|\omega'_{\rm edge}|\ge n(p_c-3\theta)$.
--
--   Probabilities of these events are taken for independent $\omega,\omega'$ from $\hat\pi^+$ or $\hat\pi^-$. They are the objects of Theorem 21.
--
--   **Formalization Note** The paper fixes no tie-break for the largest component, so the lifted plus law takes a choice function $c$ selecting a component of maximum size, and Theorem 21 quantifies over every such choice. Components and tree excess reuse the published `components`, `edgesIn` and `exc` of the base mission. $R$ is a real number.
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), §5.1, p.22; §5.2, (26) and H±_θ, p.23

import Mathlib
import Definitions.Def_LowTempGlauber_Disagreement
import Definitions.Def_LowTempGlauber_Supplement_RandomCluster

open Classical

namespace LowTempGlauber.Supplement

/-!
# Lifted random-cluster configurations `Ω`, the laws `π̂, π̂^±`, and the events of Theorem 21

A. Galanis, D. Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission manuscript dated 3 November 2026 (held version, sha256 c41a38ff…7533d), §5.1, p.22, and
§5.2, (26) and `H^±_θ`, p.23.

**Formalization Note.**
* A lifted configuration is `ω = (F, S)` with `F : G.edgeSet → Bool` (`ω_edge`) and `S ⊆ Fin n`
  (`ω_ver`, the active vertices). `Compatible G ω`: every edge of `F` has both endpoints in `S` or both
  outside `S`, i.e. `S` is a union of components of `(V, F)` (p.22).
* `kappa0 G ω = κ₀(ω)`, the number of components of `(V∖S, ω_inact)`, `ω_inact` the edges of `F` with
  both ends in `V∖S`: the components (published `LowTempGlauber.components`) of the graph `(V, F)`
  induced on `V∖S`.
* `liftLaw G β q ω ∝ (e^β − 1)^{|F|} (q − 1)^{κ₀(ω)}` on `Ω`, `0` off `Ω` (p.22).
* `IsLargestChoice G c`: `c F` is a component of `(V, F)` of maximum size. The paper does not fix a
  tie-break for "the largest component `C₁(ω)`", so Theorem 21 is stated for every such choice.
* `liftPlus G β q d c ω = q · π̂(ω | Ω⁺) · 1{C₁(ω) ⊆ S}` and `liftMinus G β q d = π̂(· | Ω⁻)`, with
  `Ω^± = {(F, S) ∈ Ω : F ∈ E^±_G}` (p.22).
* `inactExc G ω` is the total tree excess `|ω_inact| − |V∖S| + κ₀(ω)` of the inactive graph
  `(V, ω_inact)` (isolated vertices of `S` add `1` to both `|V|` and the component count).
* `EventA G R ω ω'` is `A_{G,R}`: one of the two inactive graphs has tree excess `> R` (`R` real).
* `EventB G ℓ r ω ω'` is `B_{G,ℓ,r}`: some component `C` of `H(ω, ω')`, the subgraph of
  `(V, F ∪ F')` induced by `D = S ⊕ S'`, has `|V(C)| > ℓ` or `exc(C) = |E(C)| − |V(C)| + 1 > r`
  (published `LowTempGlauber.exc`).
* `HPlus d q θ ω ω'` is `H⁺_θ`: both in `Ω⁺` and `|ω_edge| ≤ n(p_c + 3θ)` or `|ω'_edge| ≤ n(p_c + 3θ)`;
  `HMinus` is `H⁻_θ`: both in `Ω⁻` and one of them has `≥ n(p_c − 3θ)` edges.
* `pairProb μ E = Pr[(ω, ω') ∈ E]` for independent `ω, ω' ∼ μ`.
-/

/-- A lifted configuration `ω = (ω_edge, ω_ver)`. -/
abbrev LiftCfg {n : ℕ} (G : SimpleGraph (Fin n)) := (G.edgeSet → Bool) × Finset (Fin n)

/-- `(F, S) ∈ Ω`: every edge of `F` has both ends in `S` or both outside. -/
def Compatible {n : ℕ} (G : SimpleGraph (Fin n)) (ω : LiftCfg G) : Prop :=
  ∀ e : G.edgeSet, ω.1 e = true → ∀ u ∈ (e : Sym2 (Fin n)), ∀ v ∈ (e : Sym2 (Fin n)),
    (u ∈ ω.2 ↔ v ∈ ω.2)

/-- `κ₀(ω)`: the number of components of `(V∖S, ω_inact)`. -/
noncomputable def kappa0 {n : ℕ} (G : SimpleGraph (Fin n)) (ω : LiftCfg G) : ℕ :=
  (LowTempGlauber.components (PottsRapidMixing.edgeGraph G ω.1) ω.2ᶜ).card

/-- The weight `(e^β − 1)^{|F|} (q − 1)^{κ₀(ω)}` on `Ω`, `0` off `Ω`. -/
noncomputable def liftW {n : ℕ} (G : SimpleGraph (Fin n)) (β q : ℝ) (ω : LiftCfg G) : ℝ :=
  if Compatible G ω then
    (Real.exp β - 1) ^ PottsRapidMixing.numOpen ω.1 * (q - 1) ^ kappa0 G ω
  else 0

/-- `π̂(ω) ∝ (e^β − 1)^{|ω_edge|} (q − 1)^{κ₀(ω)}` on `Ω`, p.22. -/
noncomputable def liftLaw {n : ℕ} (G : SimpleGraph (Fin n)) (β q : ℝ) (ω : LiftCfg G) : ℝ :=
  liftW G β q ω / ∑ ω' : LiftCfg G, liftW G β q ω'

/-- `c` selects, for every `F`, a component of `(V, F)` of maximum size. -/
def IsLargestChoice {n : ℕ} (G : SimpleGraph (Fin n)) (c : (G.edgeSet → Bool) → Finset (Fin n)) :
    Prop :=
  ∀ F, c F ∈ LowTempGlauber.components (PottsRapidMixing.edgeGraph G F) Finset.univ ∧
    ∀ C ∈ LowTempGlauber.components (PottsRapidMixing.edgeGraph G F) Finset.univ,
      C.card ≤ (c F).card

/-- `π̂⁺(ω) = q · π̂(ω | Ω⁺) · 1{C₁(ω) is active}`, p.22. -/
noncomputable def liftPlus {n : ℕ} (G : SimpleGraph (Fin n)) (β q : ℝ) (d : ℕ)
    (c : (G.edgeSet → Bool) → Finset (Fin n)) (ω : LiftCfg G) : ℝ :=
  q * condLaw (liftLaw G β q) (fun ω' => IsRCPlus d q ω'.1) ω * (if c ω.1 ⊆ ω.2 then 1 else 0)

/-- `π̂⁻ = π̂(· | Ω⁻)`, p.22. -/
noncomputable def liftMinus {n : ℕ} (G : SimpleGraph (Fin n)) (β q : ℝ) (d : ℕ) :
    LiftCfg G → ℝ :=
  condLaw (liftLaw G β q) (fun ω' => IsRCMinus d q ω'.1)

/-- The total tree excess of the inactive graph `(V, ω_inact)`. -/
noncomputable def inactExc {n : ℕ} (G : SimpleGraph (Fin n)) (ω : LiftCfg G) : ℤ :=
  (LowTempGlauber.edgesIn (PottsRapidMixing.edgeGraph G ω.1) ω.2ᶜ : ℤ) - (ω.2ᶜ.card : ℤ) +
    (kappa0 G ω : ℤ)

/-- `A_{G,R}`, (26): one of the inactive graphs has tree excess `> R`. -/
def EventA {n : ℕ} (G : SimpleGraph (Fin n)) (R : ℝ) (ω ω' : LiftCfg G) : Prop :=
  R < (inactExc G ω : ℝ) ∨ R < (inactExc G ω' : ℝ)

/-- `B_{G,ℓ,r}`, (26): some component of `H(ω, ω')` has more than `ℓ` vertices or tree excess `> r`. -/
def EventB {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ r : ℕ) (ω ω' : LiftCfg G) : Prop :=
  ∃ C ∈ LowTempGlauber.components
      (PottsRapidMixing.edgeGraph G (fun e => ω.1 e || ω'.1 e)) ((ω.2 \ ω'.2) ∪ (ω'.2 \ ω.2)),
    ℓ < C.card ∨
      (r : ℤ) < LowTempGlauber.exc (PottsRapidMixing.edgeGraph G (fun e => ω.1 e || ω'.1 e)) C

/-- `H⁺_θ`, p.23. -/
def HPlus {n : ℕ} {G : SimpleGraph (Fin n)} (d : ℕ) (q θ : ℝ) (ω ω' : LiftCfg G) : Prop :=
  IsRCPlus d q ω.1 ∧ IsRCPlus d q ω'.1 ∧
    ((PottsRapidMixing.numOpen ω.1 : ℝ) ≤ n * (pC q d + 3 * θ) ∨
      (PottsRapidMixing.numOpen ω'.1 : ℝ) ≤ n * (pC q d + 3 * θ))

/-- `H⁻_θ`, p.23. -/
def HMinus {n : ℕ} {G : SimpleGraph (Fin n)} (d : ℕ) (q θ : ℝ) (ω ω' : LiftCfg G) : Prop :=
  IsRCMinus d q ω.1 ∧ IsRCMinus d q ω'.1 ∧
    ((n : ℝ) * (pC q d - 3 * θ) ≤ PottsRapidMixing.numOpen ω.1 ∨
      (n : ℝ) * (pC q d - 3 * θ) ≤ PottsRapidMixing.numOpen ω'.1)

/-- `Pr[(ω, ω') ∈ E]` for independent `ω, ω' ∼ μ`. -/
noncomputable def pairProb {α : Type*} [Fintype α] (μ : α → ℝ) (E : α → α → Prop) : ℝ :=
  ∑ ω, ∑ ω', if E ω ω' then μ ω * μ ω' else 0

end LowTempGlauber.Supplement


