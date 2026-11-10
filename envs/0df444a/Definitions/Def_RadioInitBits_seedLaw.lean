-- Prove2me | Definitions.Def_RadioInitBits_seedLaw
-- name    : RadioInitBits_seedLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:09.767981+00:00
-- url     : https://prove2.me/theorems/c6f2c2a1-fce6-4f0a-bfcb-f94416dabb12
-- title:
--   Private random seeds of the nodes
-- statement:
--   The nodes of the network are identical and run the same code, so symmetry must be broken by randomness. Each node $i$ has a **private random seed** $\omega_i=(\omega_i(0),\omega_i(1),\dots)$, an infinite sequence of numbers in $[0,1]$.
--
--   The coordinates of one seed are independent and uniformly distributed on $[0,1]$. The seeds of different nodes are independent. So the joint law of $(\omega_1,\dots,\omega_n)$ is the product
--   $$\mu_n=\bigotimes_{i=1}^{n}\ \bigotimes_{k\in\mathbb N}\mathrm{Unif}[0,1].$$
--   No randomness is shared between nodes.
--
--   Every success probability in the mission is computed under $\mu_n$.
--
--   **Formalization Note** A seed is a function `ℕ → unitInterval`. Its law is the infinite product of Lebesgue measure on `unitInterval` (`Measure.infinitePi`), and the joint law of the $n$ seeds is `Measure.pi` over `Fin n`. A stream of independent uniforms is a universal source of randomness: any finite or countable sequence of coin flips or uniform choices is a measurable function of it. The law is fixed by the model. A protocol cannot choose its own source of randomness.
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), full version §2.1, p.4 (PDF p.25): "Since all nodes are identical and execute the same protocol, randomization is necessary to break symmetry."

import Mathlib

set_option autoImplicit false

namespace RadioInitBits

open MeasureTheory

/-- A node's **private random seed**: a stream `ω 0, ω 1, …` of numbers in `[0, 1]`.
D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), full version §2.1, p.4 (PDF p.25): "Since all nodes
are identical and execute the same protocol, randomization is necessary to break symmetry. We
therefore consider randomized algorithms."

**Formalization Note** The paper does not name a source of randomness. A stream of i.i.d.
uniform numbers in `[0, 1]` is a universal one: every distribution a randomized node could sample
(finitely or countably many coin flips, uniform choices from `[1, T]`) is a measurable function
of it. -/
abbrev Seed : Type := ℕ → unitInterval

/-- The law of one node's seed: the coordinates are independent and uniform on `[0, 1]`
(the infinite product of Lebesgue measure on `unitInterval`). -/
noncomputable def seedLaw : Measure Seed :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

/-- The joint law of the seeds `ω : Fin n → Seed` of the `n` nodes: independent copies of
`seedLaw`, one per node. This is **private** randomness: no randomness is shared between nodes.

**Formalization Note** The law is fixed by the model; a protocol cannot choose its own seed
space or seed distribution. -/
noncomputable def jointSeedLaw (n : ℕ) : Measure (Fin n → Seed) :=
  Measure.pi (fun _ : Fin n => seedLaw)

end RadioInitBits


