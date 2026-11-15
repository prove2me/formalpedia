-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_07_Part_2
-- name    : InfoLossLAR_NativeBundle_07_Part_2
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T15:33:50.541812+00:00
-- url     : https://prove2.me/theorems/8bbcb51b-2768-40c7-9fdf-6dc8745e1e32
-- title:
--   Cycle likelihoods and physical root-evaluation data
-- statement:
--   This package defines finite cycle and path likelihoods, complete cycle matrix contractions, root components and projections, and the polynomial evaluations used for body, paired, leg and background responses.
--
--   For a finite latent alphabet and a cycle of length $\ell\ge2$, the complete contraction retains the closing edge:
--   $$Z(A_0,\ldots,A_{\ell-1})=\sum_{x_0,\ldots,x_{\ell-1}}\prod_{i=0}^{\ell-1}A_i(x_i,x_{i+1\bmod\ell}).$$
--   Matrix energies and the selected-root and grouped-source indices provide the finite data for later response and norm theorems. The definitions describe the joint cycle experiment, including its shared latent values.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; native source modules lean/CurrentAFT/CycleForestCounting.lean, lean/CurrentAFT/CycleKernel.lean, lean/CurrentAFT/CycleJointLikelihood.lean, lean/CurrentAFT/CenteredCycleDensity.lean, lean/CurrentAFT/RareMixture.lean, lean/CurrentAFT/PairCycleDensity.lean, lean/CurrentAFT/SupportedHoeffding.lean, lean/CurrentAFT/CycleDensity.lean, lean/CurrentAFT/CycleRootParameters.lean, lean/CurrentAFT/UniformCycleSelection.lean, lean/CurrentAFT/CycleRootExpansion.lean, lean/CurrentAFT/SelectedRootComponent.lean, lean/CurrentAFT/PairedRootInput.lean, lean/CurrentAFT/PairedRootCentering.lean, lean/CurrentAFT/RootCoordinateProjection.lean, lean/CurrentAFT/PairedRootProjection.lean, lean/CurrentAFT/BodyChannelEvaluation.lean, lean/CurrentAFT/BackgroundAtomEvaluation.lean, lean/CurrentAFT/BodyPairEvaluation.lean, lean/CurrentAFT/DiffusePairEvaluation.lean, lean/CurrentAFT/MixedPairEvaluation.lean, lean/CurrentAFT/PairQuadraticEvaluation.lean, lean/CurrentAFT/LegPolynomialEvaluation.lean, lean/CurrentAFT/BackgroundPolynomialEvaluation.lean, lean/CurrentAFT/BackgroundEndpointLaw.lean, lean/CurrentAFT/RootBackgroundPolynomial.lean, lean/CurrentAFT/RootIndependentBackground.lean, lean/CurrentAFT/RootReferenceExpectation.lean. Exact oracle-selected Definition bodies; split from the unaccepted NativeBundle_07 after its recorded server timeout. Source SHA256 66bcc34449b6632c4069482c2fcf1a8b242d3d0d6157f498f72297b1a4b6e21d. Header-only transitive import reduction verified by Lean module-data and parser oracles; imported module closure and all non-import source bytes are unchanged. Alternate sparse native dependencies preserve the original non-import body bytes and all public types; this header-only packaging is recorded in sparse_live/manifest.json. Current source SHA256 66bcc34449b6632c4069482c2fcf1a8b242d3d0d6157f498f72297b1a4b6e21d. After terminalserver300sERROR, the same canonical module reexports two smaller source-unit-preserving modules. No published module is changed. Current SHA256 831e8ea7845042e8cc09287fe3465d07af833221f22e3c6ca919e6133cc472b4.

import Definitions.Def_InfoLossLAR_NativeBundle_07_Part_2_Subpart_2


