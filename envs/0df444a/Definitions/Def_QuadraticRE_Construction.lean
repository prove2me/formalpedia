-- Prove2me | Definitions.Def_QuadraticRE_Construction
-- name    : QuadraticRE_Construction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:12:54.383093+00:00
-- url     : https://prove2.me/theorems/8f072f31-408b-480e-a80a-16c974242b6f
-- title:
--   Encoding constructions and the transformation of Lemma 4.11
-- statement:
--   An **encoding construction** (Definition 3.7) produces, from public parameters $p$, an explicit description of an encoder with tape length $\rho(p)$ and output length $\ell(p)$, a deterministic decoder, and a simulator on $\tau(p)$ uniform coins. It **runs in polynomial time** if four fixed machines compute, from the encoded parameters, the description and $\tau$ (construction); from $(p,x,r)$ the encoding (encoder); from $(p,z)$ the decoder's answer; and from $(p,y,\omega)$ the simulator's output.
--
--   For Lemma 4.11, the input is a description of an encoding $H$ by monomials of degree at most three together with $1^\lambda$, $\lambda\ge1$; the output is a new description $D'$, a straight-line program $\mathrm{pre}$ from the new encoding to an estimate of $H$'s output, and a straight-line program $\mathrm{post}$ from an output of $H$ and fresh coins to a new encoding. Given a simulator law $\mathrm{Sim}_H$, the composite simulator runs $\mathrm{Sim}_H(y)$ and then $\mathrm{post}$ with fresh coins.
--
--   These objects carry the uniformity and efficiency clauses of Fact 3.4, Lemma 4.11 and Theorem 4.12.
--
--   **Formalization Note** A randomized algorithm is a deterministic function of its input and a uniform tape. The decoder sees only $(p,z)$ and the simulator only $(p,y,\omega)$. The new decoder of Lemma 4.11 is $\mathrm{Dec}_H\circ\mathrm{pre}$, so "running time of the algorithms of $H$ plus $O(M\lambda^3)$" is a bound on the sizes of $\mathrm{pre}$ and $\mathrm{post}$ with $H$'s algorithms black boxes.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Definition 3.7, pp.15–16; Lemma 4.11, p.29

import Mathlib
import Definitions.Def_QuadraticRE_PolyTimeFn

namespace QuadraticRE

/-- An encoding construction, Definition 3.7 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.15: from the public parameters `p` it
produces an encoder, given as an explicit description, a decoder and a simulator. `τ` is the number of
uniform coins of the simulator: "Random tapes consist of independent uniform bits".

**Formalization Note.** A randomized algorithm is a deterministic function of its input and a uniform
tape. `dec` sees only `(p, z)` and `sim` only `(p, y, ω)`: neither has `x` or the encoder's tape. -/
structure Construction {Par : Type} (N b : Par → ℕ) where
  ρ : Par → ℕ
  ℓ : Par → ℕ
  τ : Par → ℕ
  desc : ∀ p, Desc (N p) (ρ p) (ℓ p)
  dec : ∀ p, (Fin (ℓ p) → F2) → Option (Fin (b p) → F2)
  sim : ∀ p, (Fin (b p) → F2) → (Fin (τ p) → F2) → Fin (ℓ p) → F2

/-- "its construction, encoder, decoder and simulator run in time polynomial": four fixed machines,
whose input starts with the encoded public parameters `enc p`. The input and output strings are the
bits of the data, in order. -/
structure Construction.IsPolyTime {Par : Type} {N b : Par → ℕ} (C : Construction N b)
    (enc : Par → List Bool) : Prop where
  construct : PolyTimeFn enc (fun p => encDesc (C.desc p) ++ encNat (C.τ p))
  encoder : PolyTimeFn
    (fun a : Σ p, (Fin (N p) → F2) × (Fin (C.ρ p) → F2) => enc a.1 ++ bits a.2.1 ++ bits a.2.2)
    (fun a => bits ((C.desc a.1).eval a.2.1 a.2.2))
  decoder : PolyTimeFn
    (fun a : Σ p, (Fin (C.ℓ p) → F2) => enc a.1 ++ bits a.2)
    (fun a => encOpt (C.dec a.1 a.2))
  simulator : PolyTimeFn
    (fun a : Σ p, (Fin (b p) → F2) × (Fin (C.τ p) → F2) => enc a.1 ++ bits a.2.1 ++ bits a.2.2)
    (fun a => bits (C.sim a.1 a.2.1 a.2.2))

/-- Input of the transformation of Lemma 4.11, p.29: a description of the coordinates of `H` as sums
of monomials of degree at most three, and `λ ≥ 1`. -/
structure CubicInput where
  N : ℕ
  r : ℕ
  ℓ : ℕ
  D : Desc N r ℓ
  deg : D.DegLE 3
  lam : ℕ
  hlam : 1 ≤ lam

/-- The bit encoding of the input of Lemma 4.11: it contains `N + r + ℓ` in unary and `1^λ`. -/
def encCubicInput (q : CubicInput) : List Bool := encTokens (descTokens q.D ++ [q.lam])

/-- Output of the transformation of Lemma 4.11: the new description `D′`, a straight-line program
`pre` that maps the new encoding to an estimate of `H`'s output, and a straight-line program `post` that
maps an output of `H` and fresh coins to a new encoding. The decoder is `Dec_H ∘ pre` and the simulator
`post ∘ (Sim_H, coins)`: the reading of "the running time of the corresponding algorithms for `H` plus
`O(Mλ³)`", with `H`'s algorithms black boxes. -/
structure CubicOutput (N ℓ : ℕ) where
  ρ' : ℕ
  ℓ' : ℕ
  τ' : ℕ
  D' : Desc N ρ' ℓ'
  pre : SLP (Fin ℓ') (Fin ℓ)
  post : SLP (Fin ℓ ⊕ Fin τ') (Fin ℓ')

/-- The bit encoding of the output of the transformation. -/
def encCubicOutput {N ℓ : ℕ} (T : CubicOutput N ℓ) : List Bool :=
  encDesc T.D' ++ encNat T.τ' ++ encSLP (fun i => i.val) T.pre ++ encSLP varToken T.post

/-- The composite simulator of Lemma 4.11 on an arbitrary law `Sim_H`: run `Sim_H(y)`, then `post` on its
output and fresh coins. -/
noncomputable def CubicOutput.compSim {N ℓ : ℕ} (T : CubicOutput N ℓ) {Y : Type}
    (SimH : Y → (Fin ℓ → F2) → ℝ) (y : Y) (z' : Fin T.ℓ' → F2) : ℝ :=
  ∑ z : Fin ℓ → F2, SimH y z * prob (fun ω : Fin T.τ' → F2 => T.post.eval (Sum.elim z ω) = z')

end QuadraticRE


